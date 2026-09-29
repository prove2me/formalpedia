-- Prove2me | Theorems.Thm_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
-- name    : ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/f9a04526-0fa6-5bb6-b397-542bd7c5e23b
-- title:
--   Primitive P-integral normalisation of a bounded q-expansion
-- statement:
--   Fix a prime $p$, a non-zero modulus $M$ and a subgroup $H \le (\mathbb Z/M)^{\times}$, and let $Pl$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense of `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $Pl$. Let $g$ be a non-zero element of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123), the intermediate field of $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise image of the function field `xHFunctionFieldC ℚ M H` $\subseteq \mathbb Q((q))$. Assume $g$ is bounded at $Pl$ after scaling: there are $c_0 \in \overline{\mathbb Q}$, $c_0 \neq 0$, and $y_0 \in Pl((q))$ such that the Laurent series underlying $c_0 \cdot g$ is the coefficientwise pushforward of $y_0$ along the inclusion $Pl \hookrightarrow \overline{\mathbb Q}$ (the map `coeffMap`, which applies a ring homomorphism to every coefficient). The conclusion asserts the existence of $c \in \overline{\mathbb Q}$ with $c \neq 0$ and of $y \in Pl((q))$ such that the series underlying $c \cdot g$ is the coefficientwise image of $y$, and such that the coefficientwise reduction of $y$ along the residue map of the local ring $Pl$ is non-zero in $\kappa(Pl)((q))$.
--
--   This is the normalisation step that replaces a $q$-expansion bounded at a place $\mathfrak P \mid p$ of $\overline{\mathbb Q}$ by a constant multiple whose expansion is $\mathfrak P$-integral and primitive, so that its reduction modulo $\mathfrak P$ is a non-zero Laurent series over the residue field. It is used in the construction of homomorphisms from the Igusa ring to residue fields attached to readings of the full-level function field `xHFunctionFieldC`, and relies on the discreteness of the valuation induced by $\mathfrak P$ on a number field containing all coefficients, via [`ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime`](thm.html#ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (g : ↥(ModularCurve.xHFunctionFieldBar M H)) (hg : g ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : c₀ ≠ 0) (y₀ : LaurentSeries ↥Pl)
    (h₀ : ((c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y₀) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ y : LaurentSeries ↥Pl,
      ((c • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 := by sorry
