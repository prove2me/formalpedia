-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_ModelLine_cyclic_and_line
-- name    : GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:23.443691+00:00
-- url     : https://prove2.me/theorems/acf844b4-ede7-4997-9d44-bb157d95d6a2
-- title:
--   Model Line: cyclic and line
-- statement:
--   The Model Line construction uses the cyclic and line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CyclicAndLine.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CyclicAndLine.lean#L13-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.ModelLine

theorem GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R)))
    (Γ : AddSubgroup W) (al : W → ℂ) (φ φ' : SB (κ → R)), GoodChar ψ O u → IsModel ψ d μ S →
    (φ ≠ 0 → Cyclic S φ) ∧
      (SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ → Law S al Γ φ' → φ ≠ 0 → ∃ a : ℂ, φ' = a • φ) := by sorry
