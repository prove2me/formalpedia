-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_wigMap_omg
-- name    : GlobalTheory.WigSh.wigMap_omg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:33.041652+00:00
-- url     : https://prove2.me/theorems/e5d9da7e-68fc-4df7-8673-a29e918abbe4
-- title:
--   Wig Sh: wig Map omg
-- statement:
--   The Wig Sh construction uses the wig Map omg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegStar.lean#L113-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegStar.lean#L113-L139

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

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
open OmgContr

theorem GlobalTheory.WigSh.wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (π'' : Mx k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → (∃ (t : ℕ) (c : Fin t → Mx k r → ℂ) (L : Fin t → (Wq' →L[ℂ] Wq)), (∀ i, Formalism.FourierDecayAlt.U.IsPolyDeg (d * (r + 1)) (c i)) ∧ ∀ g, A (GlobalTheory.WigSh.omg k r z z' g) = ∑ i, c i g • L i) ∧ ∀ g ∈ UH (Hpk k r), ∀ p : Formalism.FourierDecayAlt.B.SS k r, Matrix.of p.1.1 ∈ UWset k r z → Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p.2.1 ∈ UWset k r z' → Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r → (A (GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g))).comp (π'' (Matrix.of p.2.1)⁻¹) = (π' (Matrix.of p.2.1)⁻¹).comp (A (GlobalTheory.WigSh.omg k r z z' g)) := by sorry
