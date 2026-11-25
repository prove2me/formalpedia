-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConePolar_measurable_snoc
-- name    : GlobalTheory.HCXi.ConePolar.measurable_snoc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:26.217882+00:00
-- url     : https://prove2.me/theorems/eab853af-f1cc-44fe-9c2c-964579708981
-- title:
--   Cone Polar: measurable snoc
-- statement:
--   The Cone Polar construction uses the measurable snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralHyperboloidFibration.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralHyperboloidFibration.lean#L96-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar

theorem GlobalTheory.HCXi.ConePolar.measurable_snoc (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by sorry
