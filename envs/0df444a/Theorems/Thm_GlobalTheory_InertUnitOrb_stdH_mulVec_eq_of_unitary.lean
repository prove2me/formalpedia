-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_stdH_mulVec_eq_of_unitary
-- name    : GlobalTheory.InertUnitOrb.stdH_mulVec_eq_of_unitary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:41.828802+00:00
-- url     : https://prove2.me/theorems/5cfa6486-60b6-454c-8af5-02e587f1bff5
-- title:
--   Inert Unit Orb: std H mul Vec eq of unitary
-- statement:
--   The Inert Unit Orb construction uses the std H mul Vec eq of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormMulOfHermitianModelUnitaryConj.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormMulOfHermitianModelUnitaryConj.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormMulOfHermitianModelUnitaryConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb

theorem GlobalTheory.InertUnitOrb.stdH_mulVec_eq_of_unitary {K : UQ} {n : ℕ} (u : Matrix (Fin n) (Fin n) K.E)
    (hu : (u.map K.c)ᵀ * u = 1) (a b : Fin n → K.E) :
    stdH K n (u *ᵥ a) (u *ᵥ b) = stdH K n a b := by sorry
