-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
-- name    : ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/b8ad9293-c3f8-5f2e-a2f1-7f6a5e71a59f
-- title:
--   Base change of a subfield of ℚ((q)) is its L-span
-- statement:
--   Let $L$ be a field of characteristic $0$ that is finite-dimensional over $\mathbb{Q}$, and let $F_0$ be an intermediate field of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q)) =$ `LaurentSeries ℚ`. Write `coeffEmb L` for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying $\mathbb{Q} \to L$ to each coefficient of a Hahn series, and let `laurentBaseChange L F₀` be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image of $F_0$ under `coeffEmb L`. The assertion is that every $y$ belonging to this generated field already lies in the $L$-span of the image of $F_0$: there are a natural number $n$, scalars $c : \mathrm{Fin}\,n \to L$ and Laurent series $f : \mathrm{Fin}\,n \to \mathbb{Q}((q))$ with $f_i \in F_0$ for all $i$, such that $$y = \sum_{i} \mathrm{single}_0(c_i)\cdot \mathrm{coeffEmb}_L(f_i),$$ where $\mathrm{single}_0(c)$ is the constant Laurent series with value $c$, i.e. the image of $c$ under $L \to L((q))$. No minimality or linear independence of the $c_i$ or $f_i$ is claimed.
--
--   This says that the compositum $L \cdot F_0$ inside $L((q))$ coincides with the $L$-submodule spanned by the coefficientwise image of $F_0$, so that no division or infinite process is needed to reach elements of the base change; combined with injectivity statements it expresses the linear disjointness of $L$ and $\mathbb{Q}((q))$ over $\mathbb{Q}$. It is used in the identifications of chart algebras of modular curves after base change with tensor products against `laurentBaseChange`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (y : LaurentSeries L) (hy : y ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (n : ℕ) (c : Fin n → L) (f : Fin n → LaurentSeries ℚ), (∀ i, f i ∈ F₀) ∧
      y = ∑ i, HahnSeries.single 0 (c i) * ModularCurve.coeffEmb L (f i) := by sorry
