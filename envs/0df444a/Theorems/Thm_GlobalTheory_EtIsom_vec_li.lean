-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_vec_li
-- name    : GlobalTheory.EtIsom.vec_li
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:49.443234+00:00
-- url     : https://prove2.me/theorems/d5fc3071-0cdf-450f-93f0-aad4146aa4bc
-- title:
--   Et Isom: vec li
-- statement:
--   The Et Isom construction uses the vec li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L256-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L256-L272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.EtIsom.vec_li (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) : LinearIndependent E (fun i : Fin r => X.1.1 ^ (i : ℕ) *ᵥ X.2.1) := by sorry
