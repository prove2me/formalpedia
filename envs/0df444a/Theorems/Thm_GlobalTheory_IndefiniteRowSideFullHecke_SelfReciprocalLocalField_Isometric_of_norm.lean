-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfReciprocalLocalField_Isometric_of_norm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric.of_norm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:53.34784+00:00
-- url     : https://prove2.me/theorems/5e2e4797-7e75-5399-88b2-dbcc8f78b6bc
-- title:
--   Isometric: of norm
-- statement:
--   The Isometric construction uses the of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SelfReciprocalLocalField.lean#L153-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SelfReciprocalLocalField.lean#L153-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
variable {r : ℕ} (P : SelfRecip E r)
variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric.of_norm {G : Matrix (Fin r) (Fin r) E}
    {x n : (k ⊗[maximalRealSubfield E] plus P)ˣ} (hn : n ∈ norms P k)
    (h : Isometric P k G x) : Isometric P k G (x * n : (k ⊗[maximalRealSubfield E] plus P)ˣ) := by sorry
