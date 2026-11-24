-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_jG
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.continuous_jG
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:57.300559+00:00
-- url     : https://prove2.me/theorems/dfc977c0-4540-46dd-a4ea-56c949eee78e
-- title:
--   Rg Eis Levi: continuous j G
-- statement:
--   The Rg Eis Levi construction uses the continuous j G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L236-L241

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
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.continuous_jG (σ : R →+* R) (hσ : Continuous σ) : Continuous (jG σ : GL ι R → GL (ι ⊕ ι) R) := by sorry
