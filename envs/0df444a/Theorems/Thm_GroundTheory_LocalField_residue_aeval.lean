-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residue_aeval
-- name    : GroundTheory.LocalField.residue_aeval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:29.267412+00:00
-- url     : https://prove2.me/theorems/9e67a354-9eb1-449b-a986-199909b1e039
-- title:
--   Local Field: residue aeval
-- statement:
--   The Local Field construction uses the residue aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L32-L39

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]

theorem GroundTheory.LocalField.residue_aeval [Algebra 𝓀[K] 𝓀[M]]
    (h : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[M] (residue 𝒪[K] x) =
      residue 𝒪[M] (algebraMap 𝒪[K] 𝒪[M] x))
    (P : 𝒪[K][X]) (x : 𝒪[M]) :
    residue 𝒪[M] (aeval x P) = aeval (residue 𝒪[M] x) (P.map (residue 𝒪[K])) := by sorry
