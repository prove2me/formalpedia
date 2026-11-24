-- Prove2me | Theorems.Thm_GlobalTheory_GalMean_emb_two
-- name    : GlobalTheory.GalMean.emb_two
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:49.206338+00:00
-- url     : https://prove2.me/theorems/5a277cfa-52c8-4cc5-bfb7-6be7aa25865c
-- title:
--   Gal Mean: emb two
-- statement:
--   The Gal Mean construction uses the emb two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L67-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem GlobalTheory.GalMean.emb_two {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (g : K →+* ℂ) : g = φK ∨ g = (starRingEnd ℂ).comp φK := by sorry
