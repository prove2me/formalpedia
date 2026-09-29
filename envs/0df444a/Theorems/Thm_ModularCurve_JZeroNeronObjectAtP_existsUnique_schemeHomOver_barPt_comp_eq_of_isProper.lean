-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper
-- name    : ModularCurve.JZeroNeronObjectAtP.existsUnique_schemeHomOver_barPt_comp_eq_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/098c6abb-d665-5a57-adb0-34b5c3a633a2
-- title:
--   Unique extension of a geometric generic point over a valuation ring
-- statement:
--   Let $p$ be a natural number and write $\mathbf{Z}_{(p)}$ for the subring `baseRing p` of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $p$, so that `base p` is $\operatorname{Spec}\mathbf{Z}_{(p)}$. Let $f \colon X \to \operatorname{Spec}\mathbf{Z}_{(p)}$ be a proper morphism of schemes (in universe $0$). Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ and let $\rho \colon \mathbf{Z}_{(p)} \to A$ be a ring homomorphism whose composition with the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$ is the structure map $\mathbf{Z}_{(p)} \to \overline{\mathbf{Q}}$. Let $\mathrm{pt} \colon \operatorname{Spec}\overline{\mathbf{Q}} \to X$ be a morphism with $\mathrm{pt}$ followed by $f$ equal to `genPt p`, the morphism $\operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec}\mathbf{Z}_{(p)}$ induced by the structure map. The conclusion is that there is exactly one element $s$ of `SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f`, that is exactly one morphism $s \colon \operatorname{Spec}A \to X$ satisfying $s$ followed by $f$ equals $\operatorname{Spec}\rho$, such that `barPt A`, the morphism $\operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec}A$ induced by $A \hookrightarrow \overline{\mathbf{Q}}$, followed by $s$ equals $\mathrm{pt}$.
--
--   This is the valuative criterion of properness in the form used throughout the construction of integral models over $\mathbf{Z}_{(p)}$: a $\overline{\mathbf{Q}}$-point of a proper $\mathbf{Z}_{(p)}$-scheme lying over the geometric generic point extends uniquely to an $A$-section, for $A$ a valuation subring of $\overline{\mathbf{Q}}$. It is invoked by the integral models of the modular curves $X_H$ and $X_1$ to spread out points and to compare Hecke and degeneracy morphisms, and to analyse the action of inertia on reductions of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.existsUnique_schemeHomOver_barPt_comp_eq_of_isProper
    {p : ℕ} {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : baseRing p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    (pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X) (hpt : pt ≫ f = genPt p) :
    ∃! s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ s.1 = pt := by sorry
