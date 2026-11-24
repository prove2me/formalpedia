-- Prove2me | Theorems.Thm_GlobalTheory_GeomIrr_irreducibleSpace_pullback_of_isDomain_tensor
-- name    : GlobalTheory.GeomIrr.irreducibleSpace_pullback_of_isDomain_tensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:52.793541+00:00
-- url     : https://prove2.me/theorems/c4187ea1-3834-4256-881c-ec3c435965ad
-- title:
--   Geom Irr: irreducible Space pullback of is Domain tensor
-- statement:
--   The Geom Irr construction uses the irreducible Space pullback of is Domain tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackAffineOpenOfIsDomainTens.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackAffineOpenOfIsDomainTens.lean#L11-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackAffineOpenOfIsDomainTens
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
noncomputable section
open GlobalTheory GlobalTheory.GeomIrr
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.GeomIrr.irreducibleSpace_pullback_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by sorry
