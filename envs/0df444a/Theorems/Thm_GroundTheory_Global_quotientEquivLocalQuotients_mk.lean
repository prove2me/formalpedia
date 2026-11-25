-- Prove2me | Theorems.Thm_GroundTheory_Global_quotientEquivLocalQuotients_mk
-- name    : GroundTheory.Global.quotientEquivLocalQuotients_mk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:45.533301+00:00
-- url     : https://prove2.me/theorems/09732f9b-5058-42d1-9d10-3439f190283b
-- title:
--   Global: quotient Equiv Local Quotients mk
-- statement:
--   The Global construction uses the quotient Equiv Local Quotients mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L145-L147

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

theorem GroundTheory.Global.quotientEquivLocalQuotients_mk {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientEquivLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x := by sorry

attribute [defeq] GroundTheory.Global.quotientEquivLocalQuotients_mk
