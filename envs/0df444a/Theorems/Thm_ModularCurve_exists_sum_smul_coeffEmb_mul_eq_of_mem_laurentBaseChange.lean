-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
-- name    : ModularCurve.exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7256033a-6a96-5c18-b922-edf4773845b1
-- title:
--   Elements of L· F₀ in L((q)) as fractions of finite L-combinations
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $F_0$ be an intermediate field of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$ of the field of formal Laurent series over $\mathbb{Q}$. Write [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying the structure map $\mathbb{Q} \to L$ to each coefficient, and let [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image of $F_0$ under this homomorphism. The assertion is that for every $x$ belonging to this generated field there exist a finite index type $\iota$, scalars $c : \iota \to L$ and elements $g : \iota \to F_0$, and a finite index type $\kappa$, scalars $d : \kappa \to L$ and elements $h : \kappa \to F_0$, such that the finite sum $\sum_j d_j \cdot \mathrm{coeffEmb}(h_j)$ is non-zero in $L((q))$ and $$x \cdot \sum_j d_j\,\mathrm{coeffEmb}(h_j) = \sum_i c_i\,\mathrm{coeffEmb}(g_i),$$ where the scalars act through the algebra map $L \to L((q))$. Thus $x$ is a quotient of two finite $L$-linear combinations of $q$-expansions coming from $F_0$, with non-zero denominator.
--
--   This is the standard description of an element of the compositum $L \cdot F_0$ inside $L((q))$ as a fraction of finite $L$-combinations of elements of $F_0$. It is used in the analysis of $q$-expansions of functions with coefficients in a field $L$: the finitely many coefficients $c_i, d_j$ produced here cut the situation down to a finitely generated coefficient field, and the statement is cited in the study of stalk readings on the model of the modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ModularCurve.exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
    (L : Type) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (x : LaurentSeries L) (hx : x ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → L) (g : ι → ↥F₀) (κ : Type) (_ : Fintype κ) (d : κ → L) (h : κ → ↥F₀),
      (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) ≠ 0 ∧
      x * (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) =
        ∑ i, algebraMap L (LaurentSeries L) (c i) * ModularCurve.coeffEmb L ((g i : ↥F₀) : LaurentSeries ℚ) := by sorry
