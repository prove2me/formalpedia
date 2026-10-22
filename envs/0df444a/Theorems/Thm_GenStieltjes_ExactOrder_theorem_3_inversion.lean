-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_theorem_3_inversion
-- name    : GenStieltjes.ExactOrder.theorem_3_inversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:16.715422+00:00
-- url     : https://prove2.me/theorems/5f53de90-a88c-46b7-91fa-5a4d0f38cd71
-- title:
--   Theorem 3, inversion (11), case $n=[\beta-\alpha]=0$ — recovering $\mu_\alpha$ from any $S_\beta$ representing measure
-- statement:
--   Let $0<\alpha<\beta<\alpha+1$. Let $f\in S_\alpha$ be represented by $(\mu_\infty,\mu_\alpha)$, and let $(\mu'_\infty,\mu_\beta)$ be **any** representation of the same $f$ in $S_\beta$:
--   $$f(z)=\mu_\infty+\int_{[0,\infty)}\frac{\mu_\alpha(du)}{(z+u)^\alpha}=\mu'_\infty+\int_{[0,\infty)}\frac{\mu_\beta(du)}{(z+u)^\beta},\qquad z>0 .$$
--   Then for every $y\ge0$
--   $$F_{\mu_\alpha}(y)=\frac{\Gamma(\alpha)}{\Gamma(\beta)\Gamma(\alpha-\beta+1)}\int_{[0,y)}\frac{\mu_\beta(du)}{(y-u)^{\beta-\alpha}},$$
--   where $F_{\mu_\alpha}(y)=\mu_\alpha([0,y))$, and the constants agree: $\mu_\infty=\mu'_\infty$ (the paper's $\mu_\alpha(\{\infty\})=\mu_\beta(\{\infty\})$).
--
--   This is the converse part of Theorem 3, formula (11), in the case $n=[\beta-\alpha]=0$. Because $\mu_\beta$ is an arbitrary representing measure, the statement includes the uniqueness of the representation in $S_\beta$. Both directions of Theorem 16 use it with $\beta-\alpha=\varepsilon<1$.
--
--   **Formalization Note** Only $n=0$ is stated (for $n\ge1$ the printed derivative is not defined at the jumps of $F_{\mu_\alpha}$). Both sides of the identity are valued in $[0,\infty]$.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 4, Theorem 3, formula (11) with n = 0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Theorem 3, inversion (11), case `n = [β − α] = 0`, p. 4: if `0 < α < β < α + 1`,
`f ∈ S_α` is represented by `(a, μ_α)` and `(b, μ_β)` is any representation of `f` in `S_β`,
then `F_{μ_α}(y) = Γ(α)/(Γ(β)Γ(α − β + 1)) ∫_{[0,y)} μ_β(du) / (y − u)^{β−α}` for every
`y ≥ 0`, and the constants (atoms at infinity) agree: `a = b`. -/
theorem theorem_3_inversion (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβα : β < α + 1)
    (f : PositiveReal → ℝ) (a b : ℝ) (μα μβ : Measure ℝ≥0)
    (hfα : StieltjesRepresentation α f a μα) (hfβ : StieltjesRepresentation β f b μβ) :
    (∀ y : ℝ≥0, distFn μα y =
      ENNReal.ofReal (Real.Gamma α / (Real.Gamma β * Real.Gamma (α - β + 1))) *
        ∫⁻ u in Set.Iio y, ENNReal.ofReal (((y : ℝ) - (u : ℝ)) ^ (-(β - α))) ∂μβ) ∧
      a = b := by sorry

end GenStieltjes.ExactOrder
