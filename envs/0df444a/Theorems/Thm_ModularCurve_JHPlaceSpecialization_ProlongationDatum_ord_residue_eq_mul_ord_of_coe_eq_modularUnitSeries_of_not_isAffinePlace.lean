-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d6ada920-877d-5d0b-8cb9-a44a5e6d2736
-- title:
--   Cusp orders of the residue of the modular unit Δ(q)/Δ(qᵖ)
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M =$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the level-$H$ $q$-expansion function field inside $\overline{\mathbb{Q}}((q))$; let `Psp` be a place-specialisation packet at $A$ and `Rpd` a prolongation datum over it and $\theta$, with first regular prolongation $R_1$, its subring of integers and residue map into $\bar{F} =$ `JHNeronObjectAtP.Fbar p M H hpM κ`. Let $u \in F_M$ have $q$-expansion the image under the coefficient embedding of `modularUnitSeries p` $= \Delta \cdot \Delta_p^{-1}$, and assume $u$ is $R_1$-integral. Let $v$ be a place of $\bar{F}$ over $\kappa$ which is not affine, i.e. no element of $\bar{F}$ with $q$-expansion `jqModC` $\kappa$ has a value at $v$, and let $x_b \in \bar{F}$ have $q$-expansion `jqModC` $\kappa$. Then $\operatorname{ord}_v(\mathrm{res}_1 u) = (p-1)\,\operatorname{ord}_v(x_b)$, where $\operatorname{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   The function with $q$-expansion $\Delta(q)/\Delta(q^p)$ is Ogg's modular unit on $X_0(p)$, pulled back here to level $\Gamma_H(M)$; the statement computes the cusp orders of its reduction on the characteristic-$p$ fibre, expressing them as $(p-1)$ times those of the modular invariant $\bar{\jmath}$. It feeds the verification of the one-sided model laws for the Deligne–Rapoport-style reduction of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (h₁ : u ∈ Rpd.R₁.integers)

    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = ((p : ℤ) - 1) * v.ord xb := by sorry
