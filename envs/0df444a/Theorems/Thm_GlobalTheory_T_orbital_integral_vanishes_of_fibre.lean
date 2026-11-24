-- Prove2me | Theorems.Thm_GlobalTheory_T_orbital_integral_vanishes_of_fibre
-- name    : GlobalTheory.T.orbital_integral_vanishes_of_fibre
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:54:34.519041+00:00
-- url     : https://prove2.me/theorems/43dd855e-4b14-46b5-9f41-62f6b13bd977
-- title:
--   T: orbital integral vanishes of fibre
-- statement:
--   The T construction uses the orbital integral vanishes of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitalIntegralVanishesOfFibreStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitalIntegralVanishesOfFibreStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibre
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibreStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.orbital_integral_vanishes_of_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by sorry
