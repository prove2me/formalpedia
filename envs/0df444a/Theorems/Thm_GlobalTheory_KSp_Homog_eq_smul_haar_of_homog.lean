-- Prove2me | Theorems.Thm_GlobalTheory_KSp_Homog_eq_smul_haar_of_homog
-- name    : GlobalTheory.KSp.Homog.eq_smul_haar_of_homog
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:16.720349+00:00
-- url     : https://prove2.me/theorems/f25c14dc-23d1-405c-8f35-270b9cee7ec8
-- title:
--   Homog: eq smul haar of homog
-- statement:
--   The Homog construction uses the eq smul haar of homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L214-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L214-L241

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.KSp.Homog.eq_smul_haar_of_homog : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n],
    n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) →
    ∃ r : NNReal, n = r • lam := by sorry
