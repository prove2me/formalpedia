-- Prove2me | Theorems.Thm_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
-- name    : ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/9ddc8ba1-3a65-55e1-9e4e-c09938f32cec
-- title:
--   Base change of a subfield of ℚ((q)) as an L-span
-- statement:
--   Let $L$ be a field of characteristic zero, let $\iota$ be a finite index type and let $b : \iota \to L$ be a basis of $L$ as a $\mathbb{Q}$-vector space. Let $F_0$ be an intermediate field of the extension $\mathbb{Q}((q))/\mathbb{Q}$, where $\mathbb{Q}((q))$ denotes the field `LaurentSeries ℚ` of Laurent series, and write $\iota_L =$ [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying the structure map $\mathbb{Q} \to L$ to each coefficient. Then for a Laurent series $f \in L((q))$ the following are equivalent: $f$ lies in [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103), that is, in the intermediate field of $L((q))/L$ generated over $L$ by the image $\iota_L(F_0)$; and there is a family $h : \iota \to F_0$ with
--   $$f = \sum_{i \in \iota} b_i \cdot \iota_L(h_i),$$
--   the products being taken with respect to the action of $L$ on $L((q))$ by scalars. No uniqueness of the family $h$ is asserted.
--
--   This identifies the compositum $L \cdot F_0$ inside $L((q))$ with the $L$-span of $\iota_L(F_0)$, and so gives normal forms $\sum_i b_i h_i$ with $h_i \in F_0$ for elements of a base-changed function field of a modular curve. It is used in the treatment of the fields of Laurent-series expansions attached to $X_1$ and $X_1(\Gamma_0(p))$, in particular for Gauss-type reductions of points and functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
    (L : Type) [Field L] [CharZero L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries L) :
    f ∈ ModularCurve.laurentBaseChange L F₀ ↔
      ∃ h : ι → ↥F₀, f = ∑ i, (b i) • ModularCurve.coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by sorry
