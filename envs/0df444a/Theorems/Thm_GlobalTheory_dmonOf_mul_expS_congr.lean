-- Prove2me | Theorems.Thm_GlobalTheory_dmonOf_mul_expS_congr
-- name    : GlobalTheory.dmonOf_mul_expS_congr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:44:54.032296+00:00
-- url     : https://prove2.me/theorems/7eb3cfce-c30c-4819-b818-0948f80254ec
-- title:
--   Global Theory: dmon Of mul exp S congr
-- statement:
--   The Global Theory construction uses the dmon Of mul exp S congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L134-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L134-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
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
open GlobalTheory

theorem GlobalTheory.dmonOf_mul_expS_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by sorry
