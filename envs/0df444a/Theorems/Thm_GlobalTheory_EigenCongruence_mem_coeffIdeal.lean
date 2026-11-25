-- Prove2me | Theorems.Thm_GlobalTheory_EigenCongruence_mem_coeffIdeal
-- name    : GlobalTheory.EigenCongruence.mem_coeffIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:27.784538+00:00
-- url     : https://prove2.me/theorems/d6faca8d-b988-4566-8487-e2e61d71f439
-- title:
--   Eigen Congruence: mem coeff Ideal
-- statement:
--   The Eigen Congruence construction uses the mem coeff Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L31-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.EigenCongruence
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.EigenCongruence.mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R} :
    g ∈ coeffIdeal I ↔ ∀ mo, coeff mo g ∈ I := by sorry
