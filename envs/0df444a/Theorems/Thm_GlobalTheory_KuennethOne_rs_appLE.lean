-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
-- name    : GlobalTheory.KuennethOne.rs_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:05.206149+00:00
-- url     : https://prove2.me/theorems/1e6f6393-c8f7-463d-8cd4-3180c1ef00d6
-- title:
--   Kuenneth One: rs app LE
-- statement:
--   The Kuenneth One construction uses the rs app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L30-L34

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

theorem GlobalTheory.KuennethOne.rs_appLE {T : Scheme.{0}} (f : T ⟶ Z) {U : Z.Opens} {N M : T.Opens} (h : M ≤ N)
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, U)) :
    rs h ((f.appLE U N e).hom x) = (f.appLE U M (h.trans e)).hom x := by sorry
