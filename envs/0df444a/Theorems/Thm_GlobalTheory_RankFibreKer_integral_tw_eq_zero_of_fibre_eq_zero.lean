-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_integral_tw_eq_zero_of_fibre_eq_zero
-- name    : GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:46.326337+00:00
-- url     : https://prove2.me/theorems/2d84e8f0-7210-40bf-8d1f-d001603340f0
-- title:
--   Rank Fibre Ker: integral tw eq zero of fibre eq zero
-- statement:
--   The Rank Fibre Ker construction uses the integral tw eq zero of fibre eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitalIntegralVanishesOfFibre.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitalIntegralVanishesOfFibre.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer

theorem GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by sorry
