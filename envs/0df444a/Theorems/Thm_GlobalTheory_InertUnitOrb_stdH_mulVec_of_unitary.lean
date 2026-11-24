-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_stdH_mulVec_of_unitary
-- name    : GlobalTheory.InertUnitOrb.stdH_mulVec_of_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:45.321395+00:00
-- url     : https://prove2.me/theorems/f444b98a-db77-4ff2-9f8b-f2478f1346ff
-- title:
--   Inert Unit Orb: std H mul Vec of unitary
-- statement:
--   The Inert Unit Orb construction uses the std H mul Vec of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitary.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitary.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsModelOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
open GlobalTheory GlobalTheory.InertUnitOrb

theorem GlobalTheory.InertUnitOrb.stdH_mulVec_of_unitary (K : UQ) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (hγ : (γ.map K.c)ᵀ * γ = 1) (y z : Fin n → K.E) :
    stdH K n (γ *ᵥ y) (γ *ᵥ z) = stdH K n y z := by sorry
