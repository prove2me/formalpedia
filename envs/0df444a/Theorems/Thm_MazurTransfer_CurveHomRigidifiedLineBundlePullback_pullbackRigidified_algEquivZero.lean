-- Prove2me | Theorems.Thm_MazurTransfer_CurveHomRigidifiedLineBundlePullback_pullbackRigidified_algEquivZero
-- name    : MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackRigidified_algEquivZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T07:40:37.834397+00:00
-- url     : https://prove2.me/theorems/ecb079d4-ec0a-453a-b11a-88393d7cf34d
-- title:
--   Pointed curve pullback preserves fibrewise algebraic equivalence to zero
-- statement:
--   Let $C$ and $C^{\prime}$ be schemes over a commutative ring $R$, with sections $\varepsilon$ and $\varepsilon^{\prime}$. Let $f:C^{\prime}\to C$ be an $R$-morphism with $f\varepsilon^{\prime}=\varepsilon$. For any $T\to\operatorname{Spec}R$ and rigidified line bundle $M$ on $C_T$, fibrewise algebraic equivalence to zero is preserved by the specified pullback: $$M\text{ fibrewise algebraically equivalent to zero}\;\Longrightarrow\;f_T^*M\text{ fibrewise algebraically equivalent to zero}.$$ This supplies the membership condition needed to transport the actual relative Picard representation along a pointed curve isomorphism.
-- source:
--   Original thirteen-line proof and complete contract from MazurTheorem CurveHomRigidifiedLineBundlePullback.lean, Apache-2.0, Vas and contributors. Reuses the official Anthropic FLT algebraic-equivalence and module-pullback APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Structural pullback constructors are supplied by the separate public Definition. The original proof body is retained unchanged and the original complete closed type is kernel-compared with both the checked solution and public formal statement. Named downstream consumer: CurveIsoPicardRepresentationTransport and literal rational/mod-3/mod-5 fibres of the integral Picard family.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pointed curve pullback preserves the original fibrewise
algebraic-equivalence-zero predicate for rigidified line bundles.
Named downstream consumer: literal-fibre Picard representation transport.
Original line-bundle APIs: official Anthropic FLT, exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PointedCurveRigidifiedLineBundlePullback
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open MazurTransfer.CurveHomRigidifiedLineBundlePullback

theorem MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackRigidified_algEquivZero {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.val ≫ f = ε.val)
    {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (pullbackRigidified f hf hε M) := by sorry
