-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_eventuallyPoly_hilbertFun
-- name    : GlobalTheory.MultiHilbert.eventuallyPoly_hilbertFun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:10.80282+00:00
-- url     : https://prove2.me/theorems/6c798fb5-5ec9-43a1-a5c2-221a415a3a61
-- title:
--   Multi Hilbert: eventually Poly hilbert Fun
-- statement:
--   The Multi Hilbert construction uses the eventually Poly hilbert Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L389-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L389-L418

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

theorem GlobalTheory.MultiHilbert.eventuallyPoly_hilbertFun {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) :
    EventuallyPoly (hilbertFun col I) := by sorry
