-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_quotientEquivIdealRayClassGroup_mk
-- name    : GroundTheory.Global.Modulus.quotientEquivIdealRayClassGroup_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:05.553791+00:00
-- url     : https://prove2.me/theorems/ff56258d-fc4f-5b29-852f-ba1d7e3a9982
-- title:
--   Modulus: quotient Equiv Ideal Ray Class Group mk
-- statement:
--   The Modulus construction uses the quotient Equiv Ideal Ray Class Group mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L234-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean#L234-L239

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

theorem GroundTheory.Global.Modulus.quotientEquivIdealRayClassGroup_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.quotientEquivIdealRayClassGroup (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by sorry
