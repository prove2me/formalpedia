-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_smul_eq_smul_iff
-- name    : GroundTheory.Global.IdeleGroup.smul_eq_smul_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:43.61924+00:00
-- url     : https://prove2.me/theorems/b2d43e47-f23a-463e-822a-69288c86f864
-- title:
--   Idele Group: smul eq smul iff
-- statement:
--   The Idele Group construction uses the smul eq smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L204-L206

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem GroundTheory.Global.IdeleGroup.smul_eq_smul_iff {s t : IdeleGroup K} {I : 𝓘} :
    s • I = t • I ↔ toFractionalIdeal s = toFractionalIdeal t := by sorry
