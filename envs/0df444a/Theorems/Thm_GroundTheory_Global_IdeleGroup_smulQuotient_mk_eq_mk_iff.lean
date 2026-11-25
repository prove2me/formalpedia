-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_smulQuotient_mk_eq_mk_iff
-- name    : GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:37.048079+00:00
-- url     : https://prove2.me/theorems/ee14044d-263b-5350-863a-7a716a70b1f4
-- title:
--   Idele Group: smul Quotient mk eq mk iff
-- statement:
--   The Idele Group construction uses the smul Quotient mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean#L182-L191

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

theorem GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff (s : IdeleGroup K) (I : 𝓘) (x y : K) :
    smulQuotient s I (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (finiteProj v s : v.adicCompletion K) * (x : v.adicCompletion K) -
        (y : v.adicCompletion K) ∈ localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by sorry
