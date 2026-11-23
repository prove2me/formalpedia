-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslateLip_seminorm_translate_sub_le
-- name    : GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:33.321894+00:00
-- url     : https://prove2.me/theorems/ea76a695-068a-43a6-a9ce-491b693ecd34
-- title:
--   Schwartz Translate Lip: seminorm translate sub le
-- statement:
--   The Schwartz Translate Lip construction uses the seminorm translate sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslationSeminormBound.lean#L9-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslationSeminormBound.lean#L9-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic
open GlobalTheory GlobalTheory.SchwartzTranslateLip

theorem GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by sorry
