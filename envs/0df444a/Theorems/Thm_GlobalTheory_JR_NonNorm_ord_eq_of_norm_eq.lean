-- Prove2me | Theorems.Thm_GlobalTheory_JR_NonNorm_ord_eq_of_norm_eq
-- name    : GlobalTheory.JR.NonNorm.ord_eq_of_norm_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:20.329499+00:00
-- url     : https://prove2.me/theorems/685f47b1-31d0-463e-a2f8-ee77cfc2f9c8
-- title:
--   Non Norm: ord eq of norm eq
-- statement:
--   The Non Norm construction uses the ord eq of norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaKEqNegOneOfNotNorm.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaKEqNegOneOfNotNorm.lean#L69-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NonNorm
open ValuativeRel GroundTheory.LocalField IntermediateField

theorem GlobalTheory.JR.NonNorm.ord_eq_of_norm_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F
    haveI := isLocalField F
    ord x = ord y := by sorry
