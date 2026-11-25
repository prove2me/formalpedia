-- Prove2me | Theorems.Thm_GlobalTheory_constantCoeff_DmonOf_congr_jet
-- name    : GlobalTheory.constantCoeff_DmonOf_congr_jet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:22.553363+00:00
-- url     : https://prove2.me/theorems/9d43c37f-7a50-4543-9880-24be69623137
-- title:
--   Global Theory: constant Coeff Dmon Of congr jet
-- statement:
--   The Global Theory construction uses the constant Coeff Dmon Of congr jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L69-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory

theorem GlobalTheory.constantCoeff_DmonOf_congr_jet :
    ∀ (k : Type) [CommRing k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
      (u : ι → Fin d → k) (m : ι →₀ ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) →
      constantCoeff (DmonOf F u m f) = constantCoeff (DmonOf F u m g) := by sorry
