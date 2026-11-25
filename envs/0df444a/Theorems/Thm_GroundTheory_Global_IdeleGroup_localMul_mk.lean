-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_localMul_mk
-- name    : GroundTheory.Global.IdeleGroup.localMul_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:34.276596+00:00
-- url     : https://prove2.me/theorems/31ec41f9-cf2e-50c0-9f0f-c7a46d1eb559
-- title:
--   Idele Group: local Mul mk
-- statement:
--   The Idele Group construction uses the local Mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L163-L167

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

theorem GroundTheory.Global.IdeleGroup.localMul_mk (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    localMul s I v (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((finiteProj v s : v.adicCompletion K) * y) := by sorry
