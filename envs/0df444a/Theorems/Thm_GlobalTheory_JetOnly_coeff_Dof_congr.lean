-- Prove2me | Theorems.Thm_GlobalTheory_JetOnly_coeff_Dof_congr
-- name    : GlobalTheory.JetOnly.coeff_Dof_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:35.169397+00:00
-- url     : https://prove2.me/theorems/5865644e-97cc-4fac-a1ef-8f50398f9e2d
-- title:
--   Jet Only: coeff Dof congr
-- statement:
--   The Jet Only construction uses the coeff Dof congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L12-L26

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

theorem GlobalTheory.JetOnly.coeff_Dof_congr (F : Fin d → PS k 2 d) (v : Fin d → k) (n : ℕ) (f g : PS k 1 d)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + 1 → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (Dof F v f) = coeff mo (Dof F v g) := by sorry
