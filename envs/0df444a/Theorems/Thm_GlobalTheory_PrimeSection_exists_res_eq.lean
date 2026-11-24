-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_exists_res_eq
-- name    : GlobalTheory.PrimeSection.exists_res_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:09.601588+00:00
-- url     : https://prove2.me/theorems/918f3785-7434-471c-8cdb-8fc12b0f0e5b
-- title:
--   Prime Section: exists res eq
-- statement:
--   The Prime Section construction uses the exists res eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L235-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L235-L292

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
include hη

theorem GlobalTheory.PrimeSection.exists_res_eq {W : X.Opens} (r : Γ(X, W ⊓ X.basicOpen t))
    (hr : ∀ h : η ∈ W, ∃ z : X.presheaf.stalk η, algebraMap _ X.functionField z =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp h) r) :
    ∃ s : Γ(X, W), X.presheaf.map (homOfLE inf_le_left).op s = r := by sorry
