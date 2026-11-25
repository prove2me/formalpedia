-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_iSup_atoms_eq_top
-- name    : GlobalTheory.ClassFin.iSup_atoms_eq_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:04.309534+00:00
-- url     : https://prove2.me/theorems/c1a69a13-8134-5f0b-bc22-1bdb95073ef0
-- title:
--   Class Fin: i Sup atoms eq top
-- statement:
--   The Class Fin construction uses the i Sup atoms eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L61-L82

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

theorem GlobalTheory.ClassFin.iSup_atoms_eq_top [FiniteDimensional ℂ V] (h : ρ.IsSemisimpleRepresentation) :
    (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) = ⊤ := by sorry
