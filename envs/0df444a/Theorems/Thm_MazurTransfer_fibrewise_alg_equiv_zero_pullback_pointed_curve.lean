-- Prove2me | Theorems.Thm_MazurTransfer_fibrewise_alg_equiv_zero_pullback_pointed_curve
-- name    : MazurTransfer.fibrewise_alg_equiv_zero_pullback_pointed_curve
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T11:43:03.291978+00:00
-- url     : https://prove2.me/theorems/d760e1a7-27b4-4622-8d0a-8e40eeb39f12
-- title:
--   Pointed curve pullback preserves fibrewise algebraic equivalence to zero
-- statement:
--   Let $C$ and $C′$ be curves over $\operatorname{Spec}(R)$, with chosen sections. Suppose a morphism $f:C′\to C$ is over the base and carries the chosen section of $C′$ to that of $C$. For any scheme $T$ over the base, the pullback of a rigidified line bundle on $C\times_R T$ is a rigidified line bundle on $C′\times_R T$. If the original bundle is algebraically equivalent to zero on every geometric fibre, so is its pullback. The statement assumes neither properness nor smoothness and does not require $f$ to be an isomorphism. It supplies the algebraic-equivalence condition needed to transport the actual integral Picard representation to its literal rational and finite-field curve fibres.
-- source:
--   Owned proof CurveHomRigidifiedLineBundlePullback.lean in the MazurTheorem campaign. Uses the complete original rigidified-line-bundle and algebraic-equivalence pullback interface from official Anthropic FLT at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Named consumer: CurveIsoPicardRepresentationTransport and the same-family integral Picard fibres; main Mazur targets unchanged.

import Mathlib
import Definitions.Def_MazurTransfer_PointCurveRigidifiedPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open PointCurveRigidifiedPullbackLibrary.MazurTransfer.CurveHomRigidifiedLineBundlePullback
universe u

theorem MazurTransfer.fibrewise_alg_equiv_zero_pullback_pointed_curve (R : Type u) [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.val ≫ f = ε.val)
    {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (pullbackRigidified f hf hε M) := by sorry
