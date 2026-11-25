-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_LFunction_eq_tsum_coeffTerm
-- name    : GroundTheory.Global.HeckeCharacter.LFunction_eq_tsum_coeffTerm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:33.608658+00:00
-- url     : https://prove2.me/theorems/4707cee6-abcf-4c14-b4bf-d1aa304465a9
-- title:
--   Hecke Character: LFunction eq tsum coeff Term
-- statement:
--   The Hecke Character construction uses the LFunction eq tsum coeff Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L388-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L388-L390

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.LFunction_eq_tsum_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = ∑' I, χ.coeffTerm s I := by sorry
