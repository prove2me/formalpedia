-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_units_adicCompletionIntegers
-- name    : GroundTheory.Global.IdeleGroup.isOpen_units_adicCompletionIntegers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:06.050447+00:00
-- url     : https://prove2.me/theorems/0eb4fb76-a915-417d-a592-343c4c0b6b51
-- title:
--   Idele Group: is Open units adic Completion Integers
-- statement:
--   The Idele Group construction uses the is Open units adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean#L79-L82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.isOpen_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) := by sorry
