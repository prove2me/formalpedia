-- Prove2me | Theorems.Thm_GlobalTheory_T_schrodinger_product_euclidean_models_agree
-- name    : GlobalTheory.T.schrodinger_product_euclidean_models_agree
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:49.279002+00:00
-- url     : https://prove2.me/theorems/0f0e8b7f-f6f2-45fd-92d0-bad5da495c8d
-- title:
--   T: schrodinger product euclidean models agree
-- statement:
--   The T construction uses the schrodinger product euclidean models agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerProductEuclideanModelsAgreeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerProductEuclideanModelsAgreeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerProductEuclideanModelsAgree
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerProductEuclideanModelsAgreeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schrodinger_product_euclidean_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by sorry
