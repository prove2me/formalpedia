-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_uH_pk
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.uH_pk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:41.831583+00:00
-- url     : https://prove2.me/theorems/01218d91-1144-42c0-8cb3-f3dec5ac312e
-- title:
--   Rg Eis Levi QUnit: u H pk
-- statement:
--   The Rg Eis Levi QUnit construction uses the u H pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L703-L720
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L703-L720

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.uH_pk {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hE : ExtLaw) (hL : A.GoodL)
    [T2Space (A.U ε κ)] (hK : IsCompact (A.uK ε κ : Set (A.U ε κ))) (hI : Iwa (A.uQ ε S) (A.uK ε κ))
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (k : A.U ε κ) (hk : k ∈ A.uK ε κ) :
    A.uH ε S (p * k) = A.lg (bdet (Sum.inl '' S) p.1) := by sorry
