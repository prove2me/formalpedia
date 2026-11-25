-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_phi_mul_conj
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.phi_mul_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:43.636087+00:00
-- url     : https://prove2.me/theorems/c3df6fe8-7e68-5043-9968-65e14b1e8c3f
-- title:
--   Psi Volume: phi mul conj
-- statement:
--   The Psi Volume construction uses the phi mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L57-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L57-L85

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.phi_mul_conj (O : Subring F) (ϖ : F) {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1)
    {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F)
    (x : Matrix (Fin (r + d)) (Fin (r + c)) F) :
    phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) * conj (phiQ O ϖ δ r d c x) =
      (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)).indicator (fun _ => (1 : ℂ)) x := by sorry
