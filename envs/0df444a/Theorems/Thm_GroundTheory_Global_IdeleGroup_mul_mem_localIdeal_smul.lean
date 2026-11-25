-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_mul_mem_localIdeal_smul
-- name    : GroundTheory.Global.IdeleGroup.mul_mem_localIdeal_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:41.628275+00:00
-- url     : https://prove2.me/theorems/f6615e30-9da7-46ef-bf9c-17854322f797
-- title:
--   Idele Group: mul mem local Ideal smul
-- statement:
--   The Idele Group construction uses the mul mem local Ideal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L193-L198

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
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

theorem GroundTheory.Global.IdeleGroup.mul_mem_localIdeal_smul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    {w : v.adicCompletion K} (hw : w ∈ localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v) :
    (finiteProj v s : v.adicCompletion K) * w ∈
      localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by sorry
