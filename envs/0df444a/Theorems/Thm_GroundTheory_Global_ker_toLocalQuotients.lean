-- Prove2me | Theorems.Thm_GroundTheory_Global_ker_toLocalQuotients
-- name    : GroundTheory.Global.ker_toLocalQuotients
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:42.094035+00:00
-- url     : https://prove2.me/theorems/44054b90-0c6b-5084-9245-c26947c01432
-- title:
--   Global: ker to Local Quotients
-- statement:
--   The Global construction uses the ker to Local Quotients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L88-L91

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

theorem GroundTheory.Global.ker_toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    LinearMap.ker (toLocalQuotients hI) = (I : Submodule (𝓞 K) K) := by sorry
