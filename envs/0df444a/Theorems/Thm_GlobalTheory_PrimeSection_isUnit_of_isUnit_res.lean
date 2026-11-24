-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_isUnit_of_isUnit_res
-- name    : GlobalTheory.PrimeSection.isUnit_of_isUnit_res
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:31:58.143703+00:00
-- url     : https://prove2.me/theorems/995f41f2-24c5-4836-89fa-29e6fb19e89b
-- title:
--   Prime Section: is Unit of is Unit res
-- statement:
--   The Prime Section construction uses the is Unit of is Unit res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L296-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L296-L336

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
include hη hp

theorem GlobalTheory.PrimeSection.isUnit_of_isUnit_res {W : X.Opens} {s : Γ(X, W)}
    (hs : IsUnit (X.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen t ≤ W)).op s))
    (hsη : η ∈ W → η ∈ X.basicOpen s) : IsUnit s := by sorry
