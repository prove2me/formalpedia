-- Prove2me | Theorems.Thm_MobilePromo_lemma_2
-- name    : MobilePromo.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:00.315847+00:00
-- url     : https://prove2.me/theorems/6442b3cd-2a1f-4f42-af39-842fb623ee07
-- title:
--   Lemma 2: regret is bounded by the expected squared bid distance
-- statement:
--   Let Assumptions 1 and 3 hold. There is $K_0>0$, independent of $I$ and $T$, such that the regret under any bidding and FEFS allocation policy $\pi$ after $I$ seasons satisfies
--
--   $$
--   \mathrm{Regret}(\pi,I;\gamma^{(0)})\le K_0\,\mathbb E\Bigl[\sum_{i=1}^I\sum_{t=1}^T\sum_lq_l\bigl(b^\pi_{i,t,l}(X^\pi_{i,1},\hat X^\pi_{i,t})-b^*_{i,t,l}(\boldsymbol c_i(\hat X^\pi_{i,t});\gamma^{(0)})\bigr)^2\Bigr].
--   $$
--
--   The policy may place no bid in an active period; in a period with no active campaign both bids are $0$. This reduces the regret of any policy to how far its bids are from the clairvoyant ones.
--
--   Differences from the source:
--   - reading: the printed lemma names no assumption → Assumptions 1 and 3 are hypotheses; reason: the proof uses both (A7), and the lemma sits in the section under Assumption 3
--   - reading: the display of Regret on p.15 and the objective (P) write $\mathbb E\sum(b^\pi_{i,t,l}-e)q_ld_{i,t}$ → the display of p.16: `expCost` is the expectation of the realized cost $\sum(b-e)\mathbb 1\{\zeta_{i,t}=l\}d_{i,t}$; reason: with $d_{i,t}$ the realized win the p.15 display counts $q_l$ twice, and for $L=T=1$, $q<1$ a clairvoyant policy would have regret $(e-b^*)qp(1-q)>0$ per season; the proof uses the p.16 form
--   - encoding: the expectation over random histories → a finite sum over outcome paths `ω : Fin (I * T) → Outcome L` weighted by `pathProb`, seasons 0-based; reason: a period has finitely many outcomes; no instance changes
--   - encoding: a policy $\pi$ maps histories to a bid and an allocation (p.9), restricted here to FEFS → `Policy` is a bid rule on lists of outcomes, the allocation is built into `Season.state`; `IsAdmissible` asks for bid $0$ with no active campaign, and otherwise bid $0$ or a bid in $B$; reason: this is the class "any bidding and FEFS allocation policy"; a rule may also read the fixed schedule, which contains the campaign data of the history
--   - encoding: the recursion of p.15 writes $p_l(\gamma_l,b^\pi)$ even for a rule that places no bid in an active period → `winProb` is $0$ at bid $0$; reason: p.8: "if the platform places no bid … then no impression is won"; $0\notin B$
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma 2, p.16; proof A7–A8 (PDF 41–42)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption3
import Definitions.Def_MobilePromo_regret

set_option autoImplicit false

namespace MobilePromo

/-- Lemma 2 (SSRN 3523491, Lemma 2, p.16): there is `K₀ > 0`, independent of `I` and `T`, such that under
any bid rule with FEFS allocation,
`Regret(π, I; γ⁽⁰⁾) ≤ K₀ E[∑_{i=1}^I ∑_{t=1}^T ∑_l q_l (b^π_{i,t,l}(X^π_{i,1}, X̂^π_{i,t}) - b*_{i,t,l}(c_i(X̂^π_{i,t}); γ⁽⁰⁾))²]`.

**Formalization Note** The rule may bid `0` in an active period. Lemma 2 rests on Assumption 3 through
(A-5), which is why it appears here though the printed statement relies on it silently. -/
theorem lemma_2 (M : Model) (h1 : Assumption1 M) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {T : ℕ} (S : Schedule T) (I : ℕ), Assumption3 M S I →
      ∀ π : Policy M.L, IsAdmissible M S π → ∀ γ₀ ∈ M.Gamma0,
        regret M S π γ₀ I ≤
          K₀ * pathExp M π γ₀ (I * T) fun ω =>
            ∑ k : Fin (I * T), squaredGap M S π γ₀ (pref ω k) := by sorry

end MobilePromo
