-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_quotientEquivLocalQuotients_smulQuotient
-- name    : GroundTheory.Global.IdeleGroup.quotientEquivLocalQuotients_smulQuotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:53.398897+00:00
-- url     : https://prove2.me/theorems/41d63c92-29c5-5e00-88a9-473841ddbe5e
-- title:
--   Idele Group: quotient Equiv Local Quotients smul Quotient
-- statement:
--   The Idele Group construction uses the quotient Equiv Local Quotients smul Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L176-L180

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

theorem GroundTheory.Global.IdeleGroup.quotientEquivLocalQuotients_smulQuotient (s : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    quotientEquivLocalQuotients (s • I).ne_zero (smulQuotient s I q) =
      DFinsupp.mapRange.linearEquiv (localMul s I) (quotientEquivLocalQuotients I.ne_zero q) := by sorry
