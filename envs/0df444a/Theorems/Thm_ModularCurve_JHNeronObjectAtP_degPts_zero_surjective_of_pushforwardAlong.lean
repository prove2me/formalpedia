-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_degPts_zero_surjective_of_pushforwardAlong
-- name    : ModularCurve.JHNeronObjectAtP.degPts_zero_surjective_of_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/65445b47-822d-596d-b801-1e9bfd105b3a
-- title:
--   Surjectivity of the degeneracy push-forward on Pic⁰
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ is a non-unit of $A$, whose residue field has characteristic $p$ and is algebraically closed. Let $\Lambda$ be a `LevelData` at $p$ for $(M,H)$ over $A$ — a structure morphism $\mathrm{Spec}\,A \to \mathrm{base}\,p$ compatible with the generic point, a scheme with a relative group law over the base, and identifications of the $\overline{\mathbb{Q}}$-points with $J_{H'}(M/p)$ and of the special fibre points with $\mathrm{Pic}^0$ of the reduction — and let $O$ be a `JHNeronObjectAtP` for these data, a smooth separated commutative relative group scheme over $\mathrm{base}\,p$ with connected fibres whose generic points are identified with $J_H(M)$, equipped with Hecke and degeneracy data. Let $\alpha_H$ be a $\overline{\mathbb{Q}}$-algebra homomorphism from the base-changed function field of level $(M/p, H')$, where $H'$ is the image of $H$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, to the base-changed function field of level $(M,H)$; assume $\alpha_H$ is integral and that the bigger field is module-finite over the smaller one for the algebra structure induced by $\alpha_H$. Assume further that the map $O.\mathrm{degPts}\,0$ between the degree-zero divisor class groups (divisors being finitely supported $\mathbb{Z}$-valued functions on places over $\overline{\mathbb{Q}}$, taken modulo principal divisors inside the kernel of the degree) is given by push-forward of divisors along $\alpha_H$: whenever a degree-zero divisor $D_w$ downstairs equals the push-forward of a degree-zero divisor $D_v$ upstairs, $O.\mathrm{degPts}\,0$ sends the class of $D_v$ to the class of $D_w$. Then $O.\mathrm{degPts}\,0$ is surjective.
--
--   This is the statement that the degeneracy push-forward $\alpha_*\colon J_H(M)(\overline{\mathbb{Q}}) \to J_{H'}(M/p)(\overline{\mathbb{Q}})$, presented on divisor classes, is onto; it is used in the level-lowering arguments at $p$, where surjectivity of the map from the new level to the old level is needed to compare inertia actions, degeneracy maps and Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_degPts_zero_surjective_of_pushforwardAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.degPts_zero_surjective_of_pushforwardAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hαint : αH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw) :
    Function.Surjective (O.degPts 0) := by sorry
