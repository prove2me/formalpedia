-- Prove2me | Theorems.Thm_MobilePromo_lemma_A1_ii_iii
-- name    : MobilePromo.lemma_A1_ii_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:07.893421+00:00
-- url     : https://prove2.me/theorems/8c0efc83-e11d-4578-b9ec-74fa2e2a9dd2
-- title:
--   Lemma A.1, parts (ii), (iii): optimality conditions and $C^1$ dependence on $\mathcal{U}_{A\Gamma_l}$
-- statement:
--   Under Assumption 1, for each $(\alpha,\gamma_l)\in\mathcal U_{A\Gamma_l}$,
--
--   $$
--   \frac{\partial f^l(b_l,\alpha,\gamma_l)}{\partial b_l}\Big|_{b_l=b_l^*(\alpha,\gamma_l)}=0,\qquad\frac{\partial^2f^l(b_l,\alpha,\gamma_l)}{\partial b_l^2}\Big|_{b_l=b_l^*(\alpha,\gamma_l)}>0,
--   $$
--
--   and $b_l^*(\alpha,\gamma_l)$ and $f^l(b_l^*(\alpha,\gamma_l),\alpha,\gamma_l)$ are continuously differentiable in $\alpha$ and $\gamma_l$: every point of $\mathcal U_{A\Gamma_l}$ has an open neighbourhood $N$ in $\mathbb R\times\Gamma_l$ and a $C^1$ map $\varphi:N\to(b^{\min},b^{\max})$ that coincides with $b^*_l$ on $N\cap(\mathbb R\times\Gamma_l^{(0)})$, and $(\alpha,\gamma_l)\mapsto f^l(\varphi(\alpha,\gamma_l),\alpha,\gamma_l)$ is $C^1$ on $N$.
--
--   These are parts (ii) and (iii) of Lemma A.1 only; part (iv), monotonicity in $\alpha$, is not used by Theorem 1 and is not stated.
--
--   Differences from the source:
--   - reading: (iii): $b_l^*$ and $f^l(b_l^*,\alpha,\gamma_l)$ are continuously differentiable "on $\mathcal U_{A\Gamma_l}$" → a local $C^1$ extension to an open neighbourhood in $\mathbb R\times\Gamma_l$ of each point; reason: $\mathcal U_{A\Gamma_l}$ is not open and $\Gamma_l^{(0)}$ may have empty interior, so differentiability "on" it needs a meaning; this is what the Implicit Function Theorem gives on A2–A3
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma A.1(ii),(iii), A2 (PDF 36)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Lemma A.1, parts (ii) and (iii) (SSRN 3523491, Lemma A.1(ii),(iii), A2, PDF 36; part (iv) is not
stated): at each `(α, γ_l) ∈ UAΓ_l`, `∂f^l/∂b_l = 0` and `∂²f^l/∂b_l² > 0` at `b_l = b*_l(α, γ_l)`, and `b*_l` and
`f^l(b*_l(α, γ_l), α, γ_l)` are continuously differentiable in `α` and `γ_l`.

**Formalization Note** `UAΓ_l` is not open and `Γ_l⁽⁰⁾` may have empty interior, so part (iii) is stated in
the form the Implicit Function Theorem gives on A2–A3: every point of `UAΓ_l` has an open neighbourhood
`N` in `ℝ × Γ_l` and a `C¹` map `φ` on `N`, valued in the interior of `B`, that agrees with `b*_l` on
`N ∩ (ℝ × Γ_l⁽⁰⁾)`, with `f^l(φ, α, γ_l)` also `C¹` on `N`. -/
theorem lemma_A1_ii_iii (M : Model) (h1 : Assumption1 M) (l : Fin M.L) (x : ℝ × Param (M.n l))
    (hx : x ∈ UAΓ M l) :
    (deriv (fun b => f M l b x.1 x.2) (bStarOf M l x.1 x.2) = 0 ∧
      0 < deriv (deriv fun b => f M l b x.1 x.2) (bStarOf M l x.1 x.2)) ∧
    ∃ N : Set (ℝ × Param (M.n l)), IsOpen N ∧ x ∈ N ∧ N ⊆ Set.univ ×ˢ M.Γ l ∧
      ∃ φ : ℝ × Param (M.n l) → ℝ, ContDiffOn ℝ 1 φ N ∧
        (∀ y ∈ N, φ y ∈ Set.Ioo M.bmin M.bmax) ∧
        (∀ y ∈ N, y.2 ∈ M.Γ₀ l → φ y = bStarOf M l y.1 y.2) ∧
        ContDiffOn ℝ 1 (fun y => f M l (φ y) y.1 y.2) N := by sorry

end MobilePromo
