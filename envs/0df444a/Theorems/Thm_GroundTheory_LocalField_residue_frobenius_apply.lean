-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residue_frobenius_apply
-- name    : GroundTheory.LocalField.residue_frobenius_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:23.363485+00:00
-- url     : https://prove2.me/theorems/ec50c2a1-90de-4654-b00e-e31b346bdfae
-- title:
--   Local Field: residue frobenius apply
-- statement:
--   The Local Field construction uses the residue frobenius apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L195-L198

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
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
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)

theorem GroundTheory.LocalField.residue_frobenius_apply (h : ramificationIndex K L = 1) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L (frobenius K L h) x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K] := by sorry
