-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_contQ
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_contQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:22.425377+00:00
-- url     : https://prove2.me/theorems/4cc342e5-8729-4ce0-bbd3-332f596d2248
-- title:
--   Rg Eis Levi QUnit: bdet cont Q
-- statement:
--   The Rg Eis Levi QUnit construction uses the bdet cont Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L693-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L693-L696

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_contQ {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL) :
    ContinuousOn (fun p : A.U ε κ => bdet (Sum.inl '' S) p.1) (A.uQ ε S : Set (A.U ε κ)) := by sorry
