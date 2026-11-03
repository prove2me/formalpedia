-- Prove2me | Theorems.Thm_MobilePromo_lemma_A2
-- name    : MobilePromo.lemma_A2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:10.223844+00:00
-- url     : https://prove2.me/theorems/de60d679-0487-4157-8e32-82b8e1038b7c
-- title:
--   Lemma A.2: marginal values lie in $[b^{\min}-e,0]$
-- statement:
--   Let $\gamma\in\Gamma^{(0)}$ and let Assumption 1 hold. For every period $1\le t\le T+1$ of a season, every campaign $j$ and every state $\boldsymbol c$ with $c_j\ge1$,
--
--   $$
--   b^{\min}-e\le V_{i,t}(\boldsymbol c;\gamma)-V_{i,t}(\boldsymbol c-\boldsymbol e_j;\gamma)\le0 ,
--   $$
--
--   where $\boldsymbol e_j$ is the $j$-th unit vector. So the $\alpha=\Delta V_{i,t+1}(\boldsymbol c;\gamma)$ of every state lies in the domain $[b^{\min}-e,0]$ of $\mathcal U_{A\Gamma_l}$. Assumption 3 is not involved.
--
--   Differences from the source:
--   - generalization: $2\le t\le T+1$ → $1\le t\le T+1$; reason: the backward induction also covers $t=1$; it specializes to the printed range
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - generalization: $\boldsymbol c_i$ a state of season $i$, so $\boldsymbol c_i\le\boldsymbol W_i$ (p.8) → any $\boldsymbol c$ with $c_j\ge1$; reason: the recursion is defined for every $\boldsymbol c$ and the backward induction (A3–A5) never uses $\boldsymbol c\le\boldsymbol W$; it specializes to the printed states
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma A.2, A3 (PDF 37); proof A4–A5 (PDF 38–39)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Lemma A.2 (SSRN 3523491, Lemma A.2, A3, PDF 37): every marginal value of the dynamic program lies in
`[bmin - e, 0]`: `bmin - e ≤ V_{i,t}(c; γ) - V_{i,t}(c - e_j; γ) ≤ 0` for `γ ∈ Γ⁽⁰⁾`.

**Formalization Note** `c` is any state with `c_j ≥ 1`, whether or not `j` is active. The printed range is
`2 ≤ t ≤ T + 1`; the proof also covers `t = 1`. -/
theorem lemma_A2 (M : Model) (h1 : Assumption1 M) {T : ℕ} (S : Season T) (t : ℕ) (ht₁ : 1 ≤ t)
    (ht₂ : t ≤ T + 1) (j : Fin S.m) (c : Fin S.m → ℕ) (hc : 1 ≤ c j) (γ : M.ParamVec)
    (hγ : γ ∈ M.Gamma0) :
    M.bmin - M.e ≤ V M S γ t c - V M S γ t (Function.update c j (c j - 1)) ∧
      V M S γ t c - V M S γ t (Function.update c j (c j - 1)) ≤ 0 := by sorry

end MobilePromo
