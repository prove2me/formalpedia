-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_schemeKerStr_baseChange_props
-- name    : ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/4270e7f6-e4ad-5f4a-abb9-742fc4e07747
-- title:
--   Kernel of [m] on the Néron object over a place A
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $p$ prime and $p \nmid N_0$, a valuation subring $A$ of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` such that $p$ lies in the nonunits of $A$ (the predicate `LiesOverPrime`), a level datum $\Lambda$ of type `LevelData N₀ p A` — in particular a morphism $\sigma_A \colon \operatorname{Spec} A \to \mathrm{base}\ p$ and a relative group law $\Lambda.L$ on $\Lambda.f$ — satisfying the conjunction `IsJacobian` (abelian-scheme property bundle, commutativity, additivity and Galois equivariance of the point parametrisations, compatibility of reduction of points, and Hecke equivariance), an object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ` with its relative group law $O.L$ over $\mathrm{baseRing}\ p$, and an integer $m > 0$. Let $G_A$ be the base change of $O.L$ along $\sigma_A$ and let $G_A[m] \to \operatorname{Spec} A$ be its $m$-kernel, defined as the pullback of the $m$-fold multiplication morphism `schemeNsmul m` against the unit section over the identity of the base, with structure morphism the second projection `schemeKerStr m`. The assertion is that this structure morphism is locally of finite type, separated, quasi-compact, flat and locally quasi-finite; that there is a morphism $\pi$ from the $m$-kernel of the base change of $O.L$ along $\mathrm{resPt}\ A$ followed by $\sigma_A$ exhibiting the latter kernel's structure morphism as the pullback of `schemeKerStr m` along $\operatorname{Spec}$ of the residue map $A \to \kappa_A$; and that there exist a scheme $X_K$, a morphism $q_K \colon X_K \to \operatorname{Spec} \overline{\mathbf{Q}}$ and a morphism $\pi_K \colon X_K \to G_A[m]$ making $q_K$ the pullback of `schemeKerStr m` along $\operatorname{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$, with $X_K$ reduced.
--
--   This packages the geometric properties of the kernel of multiplication by $m$ on the identity component of the Néron model of $J_0(N_0p)$ over the valuation ring $A$ at a place above $p$, together with the identification of its special fibre as the corresponding kernel over the residue field $\kappa_A$ and the reducedness of its generic fibre over $\overline{\mathbf{Q}}$. It is the hypothesis package used by [`ModularCurve.JZeroNeronObjectAtP.natCard_finPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.natCard_finPts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_schemeKerStr_baseChange_props.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyOfFiniteType ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    IsSeparated ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    QuasiCompact ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    Flat ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    (∃ π : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ (O.L.baseChange Λ.σA).schemeKer m,
      IsPullback π ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((O.L.baseChange Λ.σA).schemeKerStr m) (Spec.map (CommRingCat.ofHom (residue ↥A)))) ∧
    (∃ (XK : Scheme.{0}) (qK : XK ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
        (πK : XK ⟶ (O.L.baseChange Λ.σA).schemeKer m),
      IsPullback πK qK ((O.L.baseChange Λ.σA).schemeKerStr m)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧ IsReduced XK) := by sorry
