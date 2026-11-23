-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_admitted_mono
-- name    : GlobalTheory.QNorm.admitted.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:20.787888+00:00
-- url     : https://prove2.me/theorems/1d202a1b-6364-49fc-af8c-ac57fb5ec5b6
-- title:
--   admitted: mono
-- statement:
--   The admitted construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L98-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.QNorm.admitted.mono {F : Type} [Field F] [NumberField F] {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (h : admitted F S) (hST : S ⊆ T) : admitted F T := by sorry
