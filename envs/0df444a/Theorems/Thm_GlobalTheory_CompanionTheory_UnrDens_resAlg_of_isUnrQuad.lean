-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_resAlg_of_isUnrQuad
-- name    : GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:52.476476+00:00
-- url     : https://prove2.me/theorems/cdf4d06d-3207-47a1-8bf0-fce787d3b90b
-- title:
--   Unr Dens: res Alg of is Unr Quad
-- statement:
--   The Unr Dens construction uses the res Alg of is Unr Quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResidueAlgebraUnramified.lean#L8-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResidueAlgebraUnramified.lean#L8-L43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by sorry
