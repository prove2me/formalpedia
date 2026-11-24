-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_app_rs
-- name    : GlobalTheory.AffineThickening.app_rs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:31.326113+00:00
-- url     : https://prove2.me/theorems/c7bac018-4ec3-406a-ac28-a9e5db7efdb2
-- title:
--   Affine Thickening: app rs
-- statement:
--   The Affine Thickening construction uses the app rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L36-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)

theorem GlobalTheory.AffineThickening.app_rs {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (i.app V).hom (rs h a) = rs (i.preimage_mono h) ((i.app U).hom a) := by sorry
