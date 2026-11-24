-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_algebraMap_germ
-- name    : GlobalTheory.PrimeSection.algebraMap_germ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:45.801811+00:00
-- url     : https://prove2.me/theorems/d21d91c2-d689-4ff8-b653-714dba369c9a
-- title:
--   Prime Section: algebra Map germ
-- statement:
--   The Prime Section construction uses the algebra Map germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L48-L52

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
variable {X : Scheme.{u}} [IsIntegral X]

theorem GlobalTheory.PrimeSection.algebraMap_germ {W : X.Opens} {x : X} (hx : x ∈ W) (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx s) =
      X.presheaf.germ W (genericPoint X) (genericPoint_mem hx) s := by sorry
