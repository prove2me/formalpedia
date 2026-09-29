-- Prove2me | Theorems.Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd
-- name    : ModularCurve.xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/105d55bf-d363-5f24-8e9c-3760beed81d6
-- title:
--   Mod-q collapse of level Γ_H(M)∩Γ₀(Mq) to level Γ_H(M)
-- statement:
--   Let $M\ge 1$ be a natural number (nonzero as a `NeZero` instance), $H$ a subgroup of $(\mathbb Z/M)^\times$, and $q$ a prime not dividing $M$. Let $\Gamma_H(M)\le \mathrm{SL}_2(\mathbb Z)$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image under the inclusion of $\Gamma_0(M)$ of the preimage of $H$ under the character `gamma0Units M`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. the image of $q$ in $\overline{\mathbb Q}$ is a nonunit of $A$, and write $k =$ `IsLocalRing.ResidueField A` for its residue field. The assertion is an equality of intermediate fields of the field of Laurent series over $k$: the field `xHTopFunctionFieldC k M H (M*q)`, that is the subfield generated over $k$ by the family `intFormRatiosC` attached to the level $\Gamma_H(M)\cap\Gamma_0(Mq)$, coincides with `xHFunctionFieldC k M H`, the subfield generated over $k$ by the family `intFormRatiosC` attached to the level $\Gamma_H(M)$.
--
--   Over a field of characteristic zero the function field of level $\Gamma_H(M)\cap\Gamma_0(q)$ is an extension of degree $q+1$ of that of level $\Gamma_H(M)$; the statement records that over the residue field at a place above $q$ the corresponding Laurent-series function fields at the cusp $\infty$ agree, which is the function-field shadow of the two-component Deligne–Rapoport reduction of $X(\Gamma_H(M)\cap\Gamma_0(q))$ at $q$. It is used in the construction of the pair of regular prolongations for `xHTopFunctionFieldC` at a prime not dividing $M$, via [`ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd`](thm.html#ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} [Fact q.Prime] (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ModularCurve.xHTopFunctionFieldC (IsLocalRing.ResidueField A) M H (M * q) =
      ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H := by sorry
