-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
-- name    : GlobalTheory.KuennethOne.appLE_rs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:17.113589+00:00
-- url     : https://prove2.me/theorems/f8c64955-8cf9-48a1-b34a-e2bd8a3a022c
-- title:
--   Kuenneth One: app LE rs
-- statement:
--   The Kuenneth One construction uses the app LE rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L24-L28

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

theorem GlobalTheory.KuennethOne.appLE_rs {T : Scheme.{0}} (f : T ⟶ Z) {U V : Z.Opens} (h : U ≤ V) {N : T.Opens}
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, V)) :
    (f.appLE U N e).hom (rs h x) = (f.appLE V N (e.trans (f.preimage_mono h))).hom x := by sorry
