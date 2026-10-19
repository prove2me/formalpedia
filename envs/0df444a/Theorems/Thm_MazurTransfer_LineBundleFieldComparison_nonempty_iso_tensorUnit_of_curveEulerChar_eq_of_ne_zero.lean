-- Prove2me | Theorems.Thm_MazurTransfer_LineBundleFieldComparison_nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
-- name    : MazurTransfer.LineBundleFieldComparison.nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:14:12.271232+00:00
-- url     : https://prove2.me/theorems/6a2a9ef6-9f04-4f36-9e55-9e3b7cecc5ed
-- title:
--   Numerical degree zero and a nonzero section trivialize an invertible sheaf over the original field
-- statement:
--   Let X be a smooth, proper, geometrically irreducible curve over an arbitrary field k, let M be an invertible sheaf, and choose a two-affine cover. If
--
--   $$\chi_k(M)=\chi_k(\mathcal O_X),\qquad 0\ne s\in H^0(X,M),$$
--
--   then M is isomorphic to the structure sheaf over k itself. No algebraic-closure assumption is imposed on k. The result supplies the principal-presentation triviality step in the kernel and injectivity of the actual geometric arithmetic-class map.
-- source:
--   Complete original MazurTheorem LineBundleTrivialityOfEulerCharacteristicAndSection.nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero, with all nine required original helpers from Anthropic FLT IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard MazurTransfer.LineBundleFieldComparison

theorem MazurTransfer.LineBundleFieldComparison.nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules))
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by sorry
