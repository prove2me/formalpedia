-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- name    : GlobalTheory.KuennethOne.rs_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:12.053437+00:00
-- url     : https://prove2.me/theorems/d5c5da67-1496-4f82-b046-400f746eb90e
-- title:
--   Kuenneth One: rs self
-- statement:
--   The Kuenneth One construction uses the rs self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L18-L22

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

theorem GlobalTheory.KuennethOne.rs_self {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : rs h x = x := by sorry
