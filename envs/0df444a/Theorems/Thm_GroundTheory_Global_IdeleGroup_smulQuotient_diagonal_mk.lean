-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_smulQuotient_diagonal_mk
-- name    : GroundTheory.Global.IdeleGroup.smulQuotient_diagonal_mk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:39.655926+00:00
-- url     : https://prove2.me/theorems/8a66670f-76de-422e-ace9-ff5e9e7dfdfc
-- title:
--   Idele Group: smul Quotient diagonal mk
-- statement:
--   The Idele Group construction uses the smul Quotient diagonal mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L233-L239

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

theorem GroundTheory.Global.IdeleGroup.smulQuotient_diagonal_mk (a : Kˣ) (I : 𝓘) (x : K) :
    smulQuotient (diagonal K a) I (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((a : K) * x) := by sorry
