-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_TorusConjProof_mat_conj_apply
-- name    : GlobalTheory.SatakeWeyl.TorusConjProof.mat_conj_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:11.491087+00:00
-- url     : https://prove2.me/theorems/526b2d69-bfb4-4c7a-806d-3efe94ea56f9
-- title:
--   Torus Conj Proof: mat conj apply
-- statement:
--   The Torus Conj Proof construction uses the mat conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryLeviCentreDiagonalConjugationEq.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryLeviCentreDiagonalConjugationEq.lean#L47-L52

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.TorusConjProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.SatakeWeyl.TorusConjProof.mat_conj_apply {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (g : GU σ r) (i j : Fin r) :
    mat (s * g * s⁻¹) i j = ϖ ^ (b i - b j) * mat g i j := by sorry
