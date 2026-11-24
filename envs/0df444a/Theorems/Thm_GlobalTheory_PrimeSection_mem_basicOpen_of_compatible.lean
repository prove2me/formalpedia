-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_mem_basicOpen_of_compatible
-- name    : GlobalTheory.PrimeSection.mem_basicOpen_of_compatible
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:26.237471+00:00
-- url     : https://prove2.me/theorems/dc3447cf-4613-422d-987e-58b8c42ed7da
-- title:
--   Prime Section: mem basic Open of compatible
-- statement:
--   The Prime Section construction uses the mem basic Open of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L375-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L375-L384

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
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
omit [IsIntegral X]

theorem GlobalTheory.PrimeSection.mem_basicOpen_of_compatible (hg : ∀ a b, IsUnit (g a b)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a b : ι} {x : X} (ha : x ∈ U a) (hb : x ∈ X.basicOpen (s b)) : x ∈ X.basicOpen (s a) := by sorry
