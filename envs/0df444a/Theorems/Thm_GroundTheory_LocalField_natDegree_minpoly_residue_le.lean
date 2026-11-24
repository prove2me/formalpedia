-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natDegree_minpoly_residue_le
-- name    : GroundTheory.LocalField.natDegree_minpoly_residue_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:18.7968+00:00
-- url     : https://prove2.me/theorems/427e7737-80be-4a24-bceb-df91deab3b3f
-- title:
--   Local Field: nat Degree minpoly residue le
-- statement:
--   The Local Field construction uses the nat Degree minpoly residue le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L87-L100

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by sorry
