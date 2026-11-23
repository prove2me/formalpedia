-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piQ_jQ
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.piQ_jQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:38.315357+00:00
-- url     : https://prove2.me/theorems/4cc97bf1-be5b-45f9-a73d-79cdea892e80
-- title:
--   Rg Eis Levi: pi Q j Q
-- statement:
--   The Rg Eis Levi construction uses the pi Q j Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L96-L99

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
variable (A : Ad E R) (ε : ℤˣ)

theorem GlobalTheory.CompanionTheory.RgEisLevi.piQ_jQ (h : ∀ x, A.σ (A.σ x) = x) (m : GL ι R) : piQ A ε (jQ A ε h m) = m := by sorry
