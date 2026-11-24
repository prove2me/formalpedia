-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_gauss_image_level
-- name    : GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:25.681056+00:00
-- url     : https://prove2.me/theorems/5197db5e-f5cf-476f-bdfc-ee6502dbcc35
-- title:
--   Scaled: gauss image level
-- statement:
--   The Scaled construction uses the gauss image level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L100-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L100-L166

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.Scaled
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by sorry
