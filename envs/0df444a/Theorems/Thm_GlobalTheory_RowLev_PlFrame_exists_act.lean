-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PlFrame_exists_act
-- name    : GlobalTheory.RowLev.PlFrame.exists_act
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:30:58.444852+00:00
-- url     : https://prove2.me/theorems/9a94af9f-a0b1-4b2e-b020-a25c99854a5e
-- title:
--   Pl Frame: exists act
-- statement:
--   The Pl Frame construction uses the exists act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L400-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L400-L420

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)

theorem GlobalTheory.RowLev.PlFrame.exists_act : ∃ ρ : I.Gf → GL (Fin N) (ZMod p),
    (∀ x ∈ I.Kset, fr.ActsAs x (ρ x : Matrix (Fin N) (Fin N) (ZMod p))) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ (x * x') = ρ x * ρ x' := by sorry
