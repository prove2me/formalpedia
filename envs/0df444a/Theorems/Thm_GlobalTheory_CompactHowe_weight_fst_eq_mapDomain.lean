-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_weight_fst_eq_mapDomain
-- name    : GlobalTheory.CompactHowe.weight_fst_eq_mapDomain
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:28.252329+00:00
-- url     : https://prove2.me/theorems/41362d0c-c164-4b24-b75a-d144953ccb55
-- title:
--   Compact Howe: weight fst eq map Domain
-- statement:
--   The Compact Howe construction uses the weight fst eq map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe

theorem GlobalTheory.CompactHowe.weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by sorry
