-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_isIrreducible_toRepresentation_of_isAtom
-- name    : GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:13:31.06859+00:00
-- url     : https://prove2.me/theorems/7739a63f-ff3a-4cf8-8e66-7bc7bf08caad
-- title:
--   Class Fin: is Irreducible to Representation of is Atom
-- statement:
--   The Class Fin construction uses the is Irreducible to Representation of is Atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L17-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L17-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodChevalley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom (σ : Subrepresentation ρ) (h : IsAtom σ) :
    σ.toRepresentation.IsIrreducible := by sorry
