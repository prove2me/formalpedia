-- Prove2me | Theorems.Thm_GlobalTheory_JetOnly_coeff_foldr_Dof_congr
-- name    : GlobalTheory.JetOnly.coeff_foldr_Dof_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:24.405206+00:00
-- url     : https://prove2.me/theorems/535fcf0e-b6ab-4c99-a758-2ee566a2e74c
-- title:
--   Jet Only: coeff foldr Dof congr
-- statement:
--   The Jet Only construction uses the coeff foldr Dof congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfCongrJet.lean#L40-L54

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

theorem GlobalTheory.JetOnly.coeff_foldr_Dof_congr (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k) (m : ι → ℕ)
    (f g : PS k 1 d) (L : List ι) :
    ∀ n : ℕ,
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (Dof F (u l))^[m l] s) g) := by sorry
