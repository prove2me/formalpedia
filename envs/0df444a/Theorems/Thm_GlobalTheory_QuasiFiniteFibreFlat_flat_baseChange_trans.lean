-- Prove2me | Theorems.Thm_GlobalTheory_QuasiFiniteFibreFlat_flat_baseChange_trans
-- name    : GlobalTheory.QuasiFiniteFibreFlat.flat_baseChange_trans
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:02.037333+00:00
-- url     : https://prove2.me/theorems/09459c71-3fec-424d-9dff-2ede6730d963
-- title:
--   Quasi Finite Fibre Flat: flat base Change trans
-- statement:
--   The Quasi Finite Fibre Flat construction uses the flat base Change trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatOfQuasiFiniteOfFlatFibres.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatOfQuasiFiniteOfFlatFibres.lean#L11-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatOfQuasiFiniteOfFlatFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.QuasiFiniteFibreFlat

theorem GlobalTheory.QuasiFiniteFibreFlat.flat_baseChange_trans (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by sorry
