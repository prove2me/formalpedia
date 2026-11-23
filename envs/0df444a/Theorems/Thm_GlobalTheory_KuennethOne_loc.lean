-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_loc
-- name    : GlobalTheory.KuennethOne.loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:59.785528+00:00
-- url     : https://prove2.me/theorems/a22ee020-6e8f-48b6-9cf9-5b245eb93866
-- title:
--   Kuenneth One: loc
-- statement:
--   The Kuenneth One construction uses the loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L43-L47

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

theorem GlobalTheory.KuennethOne.loc {J : Type} {N : Z.Opens} (W : J → Z.Opens) (hc : N ≤ iSup W) (x y : Γ(Z, N))
    (h : ∀ j, rs (inf_le_left : N ⊓ W j ≤ N) x = rs inf_le_left y) : x = y := by sorry
