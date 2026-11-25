-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgContr_isPolyDeg_prod
-- name    : GlobalTheory.WigSh.OmgContr.isPolyDeg_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:48:42.68639+00:00
-- url     : https://prove2.me/theorems/76896951-e1b9-5a56-9077-72a43e39e300
-- title:
--   Omg Contr: is Poly Deg prod
-- statement:
--   The Omg Contr construction uses the is Poly Deg prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegStar.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegStar.lean#L51-L56

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegStar
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
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgContr
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}

theorem GlobalTheory.WigSh.OmgContr.isPolyDeg_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i, U.IsPolyDeg (d i) (P i)) : U.IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by sorry
