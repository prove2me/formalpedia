-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_mem_subring
-- name    : GlobalTheory.CompanionTheory.RgEis.det_mem_subring
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:00.066888+00:00
-- url     : https://prove2.me/theorems/27d055f3-8406-4a51-9f93-f239efed0b7c
-- title:
--   Rg Eis: det mem subring
-- statement:
--   The Rg Eis construction uses the det mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L154-L157

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [Field E]

theorem GlobalTheory.CompanionTheory.RgEis.det_mem_subring {κ : Type} [Fintype κ] [DecidableEq κ] (O : Subring R) (m : Matrix κ κ R)
    (h : ∀ r c, m r c ∈ O) : m.det ∈ O := by sorry
