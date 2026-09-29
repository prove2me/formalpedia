-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/77c04b1f-f337-5aa5-a1f2-4c21cde3be80
-- title:
--   Valuative criterion: extending a ℚ̄-point over a place
-- statement:
--   Let $p$ be a prime and let $R_p$ denote the subring `baseRing p` of $\mathbf Q$ consisting of the rationals whose denominator is coprime to $p$, i.e. $\mathbf Z_{(p)}$, with `base p` $= \operatorname{Spec} R_p$. Let $A$ be a valuation subring of $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ`, and let $\rho \colon R_p \to A$ be a ring homomorphism such that the inclusion $A \hookrightarrow \overline{\mathbf Q}$ composed with $\rho$ is the structure map $R_p \to \overline{\mathbf Q}$. Let $f \colon X \to \operatorname{Spec} R_p$ be a proper morphism of schemes (in universe $0$), and let $x$ be a morphism $\operatorname{Spec}\overline{\mathbf Q} \to X$ with $x$ followed by $f$ equal to `genPt p`, the map $\operatorname{Spec}\overline{\mathbf Q} \to \operatorname{Spec} R_p$ induced by $R_p \hookrightarrow \overline{\mathbf Q}$. The assertion is that there exists a morphism $x_A \colon \operatorname{Spec} A \to X$ with $x_A$ followed by $f$ equal to $\operatorname{Spec}\rho$, and such that `barPt A`, the map $\operatorname{Spec}\overline{\mathbf Q} \to \operatorname{Spec} A$ induced by $A \hookrightarrow \overline{\mathbf Q}$, followed by $x_A$, equals $x$.
--
--   This is the existence half of the valuative criterion of properness, specialised to valuation subrings $A$ of $\overline{\mathbf Q}$ lying over $\mathbf Z_{(p)}$: a $\overline{\mathbf Q}$-point of a proper $\mathbf Z_{(p)}$-scheme spreads out to an $A$-point. It is the basic reduction step used when points of the Jacobian $J_0$ and of modular curves, given over the geometric generic fibre, are specialised at a place of $\overline{\mathbf Q}$ above $p$, and is invoked in the construction of the Néron-model data at $p$ and in the study of reduction of divisor classes there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : baseRing p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f] (x : SchemeHomOver (genPt p) f) :
    ∃ xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ xA.1 = x.1 := by sorry
