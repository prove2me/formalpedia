-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_mem_coprimeIdeals
-- name    : GroundTheory.Global.Modulus.mem_coprimeIdeals
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:19.099506+00:00
-- url     : https://prove2.me/theorems/e1228b21-3143-57da-9cb0-5dd877e22ae7
-- title:
--   Modulus: mem coprime Ideals
-- statement:
--   The Modulus construction uses the mem coprime Ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L30-L33

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)

theorem GroundTheory.Global.Modulus.mem_coprimeIdeals {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I ∈ 𝔪.coprimeIdeals ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by sorry
