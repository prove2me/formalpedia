-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_isSemisimpleRepresentation_tprod
-- name    : GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:34.139889+00:00
-- url     : https://prove2.me/theorems/781e1c4c-535b-4077-bd5f-adb1b99800cd
-- title:
--   Class Fin: is Semisimple Representation tprod
-- statement:
--   The Class Fin construction uses the is Semisimple Representation tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L123-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodChevalley.lean#L123-L163

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
open Matrix
open scoped Kronecker ComplexOrder TensorProduct

theorem GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by sorry
