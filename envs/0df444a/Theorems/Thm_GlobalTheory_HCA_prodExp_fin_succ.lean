-- Prove2me | Theorems.Thm_GlobalTheory_HCA_prodExp_fin_succ
-- name    : GlobalTheory.HCA.prodExp_fin_succ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:16.887024+00:00
-- url     : https://prove2.me/theorems/3af7b6d3-02d0-512f-8e91-13390f63a038
-- title:
--   HCA: prod Exp fin succ
-- statement:
--   The HCA construction uses the prod Exp fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L33-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GlobalTheory.HCA.prodExp_fin_succ (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin (n + 1) → 𝔤) (t : Fin (n + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by sorry
