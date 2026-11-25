-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_acyclicityLemma_depth_differentialCokernels_finiteLength
-- name    : GlobalTheory.FiniteLengthComplex.acyclicityLemma_depth_differentialCokernels_finiteLength
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:16.477817+00:00
-- url     : https://prove2.me/theorems/967e5dea-eb11-4f01-959f-c5d7206540d6
-- title:
--   Finite Length Complex: acyclicity Lemma depth differential Cokernels finite Length
-- statement:
--   The Finite Length Complex construction uses the acyclicity Lemma depth differential Cokernels finite Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L171-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L171-L202

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem GlobalTheory.FiniteLengthComplex.acyclicityLemma_depth_differentialCokernels_finiteLength [IsLocalRing R] (g : ℕ)
    (hX : ∀ i n, n < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.X i) n))
    (hH : ∀ i, IsFiniteLength R (C.homology i)) (i : ℕ) :
    (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) ∧
      (i < g → IsZero (C.homology i)) := by sorry
