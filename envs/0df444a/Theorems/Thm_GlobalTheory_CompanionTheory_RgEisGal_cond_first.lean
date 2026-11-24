-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_cond_first
-- name    : GlobalTheory.CompanionTheory.RgEisGal.cond_first
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:58:35.323562+00:00
-- url     : https://prove2.me/theorems/7914f77a-1ab8-4bd1-8959-d0547ebaefe5
-- title:
--   Rg Eis Gal: cond first
-- statement:
--   The Rg Eis Gal construction uses the cond first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L128-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L128-L145

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G]
variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}

theorem GlobalTheory.CompanionTheory.RgEisGal.cond_first (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneI (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * a g + t * h g) ∧
        Conv Γ B fun g => (h g + N * b g) - q * b g + t * h g := by sorry
