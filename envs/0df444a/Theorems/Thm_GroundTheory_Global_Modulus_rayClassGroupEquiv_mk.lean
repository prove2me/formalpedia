-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_rayClassGroupEquiv_mk
-- name    : GroundTheory.Global.Modulus.rayClassGroupEquiv_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:13.487409+00:00
-- url     : https://prove2.me/theorems/f33f2235-34b7-5357-ba63-3117e0401689
-- title:
--   Modulus: ray Class Group Equiv mk
-- statement:
--   The Modulus construction uses the ray Class Group Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L219-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L219-L228

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

theorem GroundTheory.Global.Modulus.rayClassGroupEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassGroupEquiv (QuotientGroup.mk x : 𝔪.RayClassGroup) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by sorry
