-- Prove2me | Theorems.Thm_GlobalTheory_JetOnly_coeff_iterate_Dof_congr
-- name    : GlobalTheory.JetOnly.coeff_iterate_Dof_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:26.646159+00:00
-- url     : https://prove2.me/theorems/f5a89763-fb5e-4adb-99b6-ec5f8ba1057a
-- title:
--   Jet Only: coeff iterate Dof congr
-- statement:
--   The Jet Only construction uses the coeff iterate Dof congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L28-L38

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
open GlobalTheory GlobalTheory.JetOnly
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.JetOnly.coeff_iterate_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (r : ℕ) :
    ∀ (n : ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo ((Dof F v)^[r] f) = coeff mo ((Dof F v)^[r] g) := by sorry
