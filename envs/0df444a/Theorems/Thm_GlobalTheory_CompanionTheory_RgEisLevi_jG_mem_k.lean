-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_jG_mem_k
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_k
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:13.301656+00:00
-- url     : https://prove2.me/theorems/c12621ef-c3c1-41a5-8174-8b8bd0e1cb68
-- title:
--   Rg Eis Levi: j G mem k
-- statement:
--   The Rg Eis Levi construction uses the j G mem k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L146-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L146-L181

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_k (A : Ad E R) (hO : ∀ x ∈ A.O, A.σ x ∈ A.O)
    (hφ : ∀ w x, A.φ w (A.σ x) = (starRingEnd ℂ) (A.φ w x)) (m : GL ι R) (hm : m ∈ A.kGL ι) :
    jG A.σ m ∈ A.kGL (ι ⊕ ι) := by sorry
