-- Prove2me | Theorems.Thm_GlobalTheory_exists_isClosed_specializes_mem_iff
-- name    : GlobalTheory.exists_isClosed_specializes_mem_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:31.990526+00:00
-- url     : https://prove2.me/theorems/c6ab4da3-a91a-44e0-848a-415b523eea8b
-- title:
--   Global Theory: exists is Closed specializes mem iff
-- statement:
--   The Global Theory construction uses the exists is Closed specializes mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L54-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]

theorem GlobalTheory.exists_isClosed_specializes_mem_iff (ξ : T) {ι : Type*} [Finite ι] (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {W : Set T} (hW : IsOpen W) (hξ : ξ ∈ W) :
    ∃ x : T, IsClosed ({x} : Set T) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i := by sorry
