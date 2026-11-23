-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
-- name    : GlobalTheory.KuennethOne.rs_rs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:11.2029+00:00
-- url     : https://prove2.me/theorems/58096365-5d09-4e52-8a92-2e2846776e93
-- title:
--   Kuenneth One: rs rs
-- statement:
--   The Kuenneth One construction uses the rs rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}

theorem GlobalTheory.KuennethOne.rs_rs {U V W : Z.Opens} (h : U ≤ V) (h' : V ≤ W) (x : Γ(Z, W)) :
    rs h (rs h' x) = rs (h.trans h') x := by sorry
