-- Prove2me | Theorems.Thm_GlobalTheory_EigenCongruence_pderiv_mem_coeffIdeal
-- name    : GlobalTheory.EigenCongruence.pderiv_mem_coeffIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:36.524025+00:00
-- url     : https://prove2.me/theorems/359aed16-2f22-43af-b8eb-4e7f60a6565c
-- title:
--   Eigen Congruence: pderiv mem coeff Ideal
-- statement:
--   The Eigen Congruence construction uses the pderiv mem coeff Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L34-L38

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

theorem GlobalTheory.EigenCongruence.pderiv_mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R}
    (hg : g ∈ coeffIdeal I) (s : σ) : pderiv R s g ∈ coeffIdeal I := by sorry
