-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_ratQ
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_ratQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:28.155233+00:00
-- url     : https://prove2.me/theorems/9e3afd50-a1f6-425d-a44b-5ab7441ed7de
-- title:
--   Rg Eis Levi QUnit: bdet rat Q
-- statement:
--   The Rg Eis Levi QUnit construction uses the bdet rat Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L698-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L698-L701

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_ratQ {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL)
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (hr : p ∈ A.uΓ ε κ) :
    ∃ x, bdet (Sum.inl '' S) p.1 = Units.map A.i.toMonoidHom x := by sorry
