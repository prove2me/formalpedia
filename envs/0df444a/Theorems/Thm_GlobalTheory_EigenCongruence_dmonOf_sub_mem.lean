-- Prove2me | Theorems.Thm_GlobalTheory_EigenCongruence_dmonOf_sub_mem
-- name    : GlobalTheory.EigenCongruence.dmonOf_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:56.278566+00:00
-- url     : https://prove2.me/theorems/d08dace7-a4ed-4a07-8489-9292bf4f5a61
-- title:
--   Eigen Congruence: dmon Of sub mem
-- statement:
--   The Eigen Congruence construction uses the dmon Of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean#L75-L80

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

theorem GlobalTheory.EigenCongruence.dmonOf_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} [Fintype ι]
    (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d)
    (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I) (m : ι →₀ ℕ) :
    DmonOf F u m f - C (∏ l, y l ^ m l) * f ∈ coeffIdeal I := by sorry
