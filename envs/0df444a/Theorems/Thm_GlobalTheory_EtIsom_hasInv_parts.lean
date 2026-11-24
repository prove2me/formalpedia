-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_hasInv_parts
-- name    : GlobalTheory.EtIsom.hasInv_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:48.190932+00:00
-- url     : https://prove2.me/theorems/e68a1aa8-78af-429d-b540-292f617c4d4c
-- title:
--   Et Isom: has Inv parts
-- statement:
--   The Et Isom construction uses the has Inv parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L162-L166

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
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.EtIsom.hasInv_parts {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) :
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (p i)) ∧
      ∀ i : Fin r, star X.2.1 ⬝ᵥ (X.1.1 ^ (i : ℕ) *ᵥ X.2.1) = algebraMap F E (Algebra.trace F A.K (τ ^ (i : ℕ) * a)) := by sorry
