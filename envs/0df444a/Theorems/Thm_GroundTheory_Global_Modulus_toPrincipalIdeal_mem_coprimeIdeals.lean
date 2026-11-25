-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_toPrincipalIdeal_mem_coprimeIdeals
-- name    : GroundTheory.Global.Modulus.toPrincipalIdeal_mem_coprimeIdeals
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:24.603984+00:00
-- url     : https://prove2.me/theorems/275412a2-b8af-56ea-a174-81c8540b90a0
-- title:
--   Modulus: to Principal Ideal mem coprime Ideals
-- statement:
--   The Modulus construction uses the to Principal Ideal mem coprime Ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L45-L48

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

theorem GroundTheory.Global.Modulus.toPrincipalIdeal_mem_coprimeIdeals {a : Kˣ} (ha : a ∈ 𝔪.rayUnits) :
    toPrincipalIdeal (𝓞 K) K a ∈ 𝔪.coprimeIdeals := by sorry
