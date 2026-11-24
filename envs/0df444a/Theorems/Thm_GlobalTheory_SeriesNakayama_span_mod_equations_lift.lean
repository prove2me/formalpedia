-- Prove2me | Theorems.Thm_GlobalTheory_SeriesNakayama_span_mod_equations_lift
-- name    : GlobalTheory.SeriesNakayama.span_mod_equations_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:26.378947+00:00
-- url     : https://prove2.me/theorems/e49b1d64-8dc4-4756-b7b1-c9c9f228a740
-- title:
--   Series Nakayama: span mod equations lift
-- statement:
--   The Series Nakayama construction uses the span mod equations lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L65-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L65-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama

theorem GlobalTheory.SeriesNakayama.span_mod_equations_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by sorry
