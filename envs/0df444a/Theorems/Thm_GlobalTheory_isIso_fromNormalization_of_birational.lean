-- Prove2me | Theorems.Thm_GlobalTheory_isIso_fromNormalization_of_birational
-- name    : GlobalTheory.isIso_fromNormalization_of_birational
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:06.647492+00:00
-- url     : https://prove2.me/theorems/cc8cdff1-7315-4c29-8abc-60922d5dae6b
-- title:
--   Global Theory: is Iso from Normalization of birational
-- statement:
--   The Global Theory construction uses the is Iso from Normalization of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L115-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L115-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}

theorem GlobalTheory.isIso_fromNormalization_of_birational (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.fromNormalization := by sorry
