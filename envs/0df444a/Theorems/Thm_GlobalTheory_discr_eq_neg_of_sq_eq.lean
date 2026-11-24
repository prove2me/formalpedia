-- Prove2me | Theorems.Thm_GlobalTheory_discr_eq_neg_of_sq_eq
-- name    : GlobalTheory.discr_eq_neg_of_sq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:48.095802+00:00
-- url     : https://prove2.me/theorems/c1902546-5559-48d5-a155-32baec974035
-- title:
--   Global Theory: discr eq neg of sq eq
-- statement:
--   The Global Theory construction uses the discr eq neg of sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L291-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L291-L323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem GlobalTheory.discr_eq_neg_of_sq_eq (h2 : finrank ℚ K = 2) (hsq : Squarefree d) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -d) : discr K = -d := by sorry
