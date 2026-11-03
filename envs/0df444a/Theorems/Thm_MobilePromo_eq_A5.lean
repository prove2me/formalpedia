-- Prove2me | Theorems.Thm_MobilePromo_eq_A5
-- name    : MobilePromo.eq_A5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:35.042993+00:00
-- url     : https://prove2.me/theorems/20e7c2c2-dcf4-41d1-8574-c08eed2aa268
-- title:
--   Inequality (A-5): the cost-to-go gap from any state of a season
-- statement:
--   Let Assumptions 1 and 3 hold. There is $K_0>0$, independent of $I$ and $T$, such that for every admissible bid rule $\pi$ with FEFS allocation, every $\gamma\in\Gamma^{(0)}$, every season $i$, every history $x_{i,1}$ of the earlier seasons and every within-season history $\hat x_{i,t}$,
--
--   $$
--   V^\pi_{i,t}(\hat x_{i,t};x_{i,1},\gamma)-V_{i,t}(\boldsymbol c_i(\hat x_{i,t});\gamma)\le K_0\,\mathbb E\Bigl[\sum_{\hat t=t}^T\sum_lq_l\bigl(b^\pi_{i,\hat t,l}(x_{i,1},\hat X^\pi_{i,\hat t})-b^*_{i,\hat t,l}(\boldsymbol c_i(\hat X^\pi_{i,\hat t});\gamma)\bigr)^2\Big|\hat X^\pi_{i,t}=\hat x_{i,t}\Bigr].
--   $$
--
--   This is the one-season form of Lemma 2.
--
--   **Formalization Note** Both history-dependent sides are backward recursions along the history: `Vπ` is the recursion of p.15, and `gapToGo` is the conditional expectation.
--
--   Differences from the source:
--   - encoding: the conditional expectation $\mathbb E[\,\cdot\mid\hat X^\pi_{i,t}=\hat x_{i,t}]$ → the backward recursion `gapToGo` along the history; reason: the tower property; no instance changes
--   - encoding: a policy $\pi$ maps histories to a bid and an allocation (p.9), restricted here to FEFS → `Policy` is a bid rule on lists of outcomes, the allocation is built into `Season.state`; `IsAdmissible` asks for bid $0$ with no active campaign, and otherwise bid $0$ or a bid in $B$; reason: this is the class "any bidding and FEFS allocation policy"; a rule may also read the fixed schedule, which contains the campaign data of the history
--   - encoding: the recursion of p.15 writes $p_l(\gamma_l,b^\pi)$ even for a rule that places no bid in an active period → `winProb` is $0$ at bid $0$; reason: p.8: "if the platform places no bid … then no impression is won"; $0\notin B$
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, (A-5), A7 (PDF 41); proof A7–A8 (PDF 41–42); recursion p.15

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption3
import Definitions.Def_MobilePromo_regret

set_option autoImplicit false

namespace MobilePromo

/-- Inequality (A-5) (SSRN 3523491, (A-5), A7, PDF 41): for any bid rule with FEFS allocation, from any
history `x₁` of the first `i - 1` seasons and `x̂` of the current one,
`V^π_{i,t}(x̂; x₁, γ) - V_{i,t}(c_i(x̂); γ) ≤ K₀ E[∑_{t̂=t}^T ∑_l q_l (b^π_{i,t̂,l} - b*_{i,t̂,l})² | X̂^π_{i,t} = x̂]`.

**Formalization Note** `t = x̂.length + 1`, and `r = T - x̂.length = T + 1 - t` periods are left. The two
history-dependent sides are the backward recursions `Vπ` (p.15) and `gapToGo`. The rule may place no bid
in an active period, a case the printed proof (A8) does not cover; there `K₀` must also dominate the
no-bid term, which it can because a no-bid has squared distance at least `bmin²` from `B`. -/
theorem eq_A5 (M : Model) (h1 : Assumption1 M) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {T : ℕ} (S : Schedule T) (I : ℕ), Assumption3 M S I →
      ∀ π : Policy M.L, IsAdmissible M S π → ∀ γ ∈ M.Gamma0, ∀ i < I,
        ∀ x₁ x : List (Outcome M.L), x₁.length = i * T → x.length ≤ T →
          Vπ M π γ (T - x.length) (x₁ ++ x) - V M (S i) γ (x.length + 1) ((S i).state x) ≤
            K₀ * gapToGo M S π γ (T - x.length) (x₁ ++ x) := by sorry

end MobilePromo
