-- Prove2me | Theorems.Thm_GlobalTheory_T_irreducibleSpace_pullback_affine_open_of_isDomain_tensor
-- name    : GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:16.744743+00:00
-- url     : https://prove2.me/theorems/9b6883dd-cec2-4ad4-8093-00efc0a06851
-- title:
--   T: irreducible Space pullback affine open of is Domain tensor
-- statement:
--   The T construction uses the irreducible Space pullback affine open of is Domain tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackAffineOpenOfIsDomainTens
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by sorry
