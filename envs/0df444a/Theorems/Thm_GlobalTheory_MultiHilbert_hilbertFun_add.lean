-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_hilbertFun_add
-- name    : GlobalTheory.MultiHilbert.hilbertFun_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:25.146199+00:00
-- url     : https://prove2.me/theorems/48a2ae13-7e24-44ad-aa18-a9d21ac9ba3b
-- title:
--   Multi Hilbert: hilbert Fun add
-- statement:
--   The Multi Hilbert construction uses the hilbert Fun add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L374-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L374-L387

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial

theorem GlobalTheory.MultiHilbert.hilbertFun_add {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) (i : σ) (n : Fin r → ℕ) :
    hilbertFun col I (n + Pi.single (col i) 1) =
      hilbertFun col (colonX I i) n +
        hilbertFun col (I ⊔ Ideal.span {X i}) (n + Pi.single (col i) 1) := by sorry
