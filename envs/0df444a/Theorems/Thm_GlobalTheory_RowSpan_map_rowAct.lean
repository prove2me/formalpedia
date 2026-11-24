-- Prove2me | Theorems.Thm_GlobalTheory_RowSpan_map_rowAct
-- name    : GlobalTheory.RowSpan.map_rowAct
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:52.371902+00:00
-- url     : https://prove2.me/theorems/7338060b-f1bc-427c-b6df-14de375862dd
-- title:
--   Row Span: map row Act
-- statement:
--   The Row Span construction uses the map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L384-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean#L384-L390

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

theorem GlobalTheory.RowSpan.map_rowAct {K : Type} [Field K] (φ : k →+* K) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k)
    (P : MvPolynomial (Letter T r n) k) :
    map φ (rowAct g P) = rowAct (fun σ => φ.mapMatrix (g σ)) (map φ P) := by sorry
