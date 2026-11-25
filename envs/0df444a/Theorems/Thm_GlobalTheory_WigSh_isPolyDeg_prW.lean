-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_isPolyDeg_prW
-- name    : GlobalTheory.WigSh.isPolyDeg_prW
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:39.463307+00:00
-- url     : https://prove2.me/theorems/06b5726b-8c91-5704-a282-4384e61e7d18
-- title:
--   Wig Sh: is Poly Deg pr W
-- statement:
--   The Wig Sh construction uses the is Poly Deg pr W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegPrW.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegPrW.lean#L17-L33

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

theorem GlobalTheory.WigSh.isPolyDeg_prW {N : ℕ} (k r d : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (v : Matrix (Fin N) (Fin N) ℂ → Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, U.IsPolyDeg d (fun g => v g i))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg d (fun g => D.prW k r z (v g) i) := by sorry
