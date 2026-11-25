-- Prove2me | Theorems.Thm_GlobalTheory_EllipticPoles_even_case
-- name    : GlobalTheory.EllipticPoles.even_case
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:01.175796+00:00
-- url     : https://prove2.me/theorems/f42b9c8c-8380-4294-ae6d-4f2bbd937d03
-- title:
--   Elliptic Poles: even case
-- statement:
--   The Elliptic Poles construction uses the even case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAnalyticOfTendsto.lean#L38-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAnalyticOfTendsto.lean#L38-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.EllipticPoles
variable (L : PeriodPair)

theorem GlobalTheory.EllipticPoles.even_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) (hev : ∀ z, g (-z) = g z) :
    ∃ A : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, g z = A.eval (℘[L] z) := by sorry
