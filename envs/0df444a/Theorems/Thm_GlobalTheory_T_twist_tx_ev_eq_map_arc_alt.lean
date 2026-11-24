-- Prove2me | Theorems.Thm_GlobalTheory_T_twist_tx_ev_eq_map_arc_alt
-- name    : GlobalTheory.T.twist_tx_ev_eq_map_arc_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:00:43.398278+00:00
-- url     : https://prove2.me/theorems/6f4e3fe5-1274-4b40-a964-6aa67b11850c
-- title:
--   T: twist tx ev eq map arc alt
-- statement:
--   The T construction uses the twist tx ev eq map arc alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArcStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArcStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArcStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.twist_tx_ev_eq_map_arc_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by sorry
