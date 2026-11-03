-- Prove2me | Theorems.Thm_MobilePromo_lemma_A1_i
-- name    : MobilePromo.lemma_A1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:59.25033+00:00
-- url     : https://prove2.me/theorems/1b9f8ab9-2d83-48a5-a245-2e40c51e5659
-- title:
--   Lemma A.1(i): $b^*_l(\alpha,\gamma_l)$ is unique
-- statement:
--   Let $l$ be a location, $\alpha\in\mathbb R$ and $\gamma_l\in\Gamma_l^{(0)}$. Under Assumption 1, the function $b_l\mapsto f^l(b_l,\alpha,\gamma_l)=p_l(\gamma_l,b_l)(b_l-e-\alpha)$ has exactly one minimizer $b_l^*(\alpha,\gamma_l)$ on $B$.
--
--   This makes the optimal bid (7) well defined for every marginal value, with no restriction on $\alpha$.
--
--   Differences from the source:
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma A.1(i), A1 (PDF 35)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Lemma A.1(i) (SSRN 3523491, Lemma A.1(i), A1, PDF 35): for each `(α, γ_l) ∈ ℝ × Γ_l⁽⁰⁾`, the minimizer
`b*_l(α, γ_l)` of `f^l(·, α, γ_l)` over `B` is unique. -/
theorem lemma_A1_i (M : Model) (h1 : Assumption1 M) (l : Fin M.L) (α : ℝ) (γl : Param (M.n l))
    (hγ : γl ∈ M.Γ₀ l) :
    ∃! b, b ∈ M.B ∧ ∀ b' ∈ M.B, f M l b α γl ≤ f M l b' α γl := by sorry

end MobilePromo
