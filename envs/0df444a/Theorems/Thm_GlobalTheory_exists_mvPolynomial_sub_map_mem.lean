-- Prove2me | Theorems.Thm_GlobalTheory_exists_mvPolynomial_sub_map_mem
-- name    : GlobalTheory.exists_mvPolynomial_sub_map_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:56:37.894797+00:00
-- url     : https://prove2.me/theorems/89290baa-0cb1-4267-91fb-25ca03dd32e1
-- title:
--   Global Theory: exists mv Polynomial sub map mem
-- statement:
--   The Global Theory construction uses the exists mv Polynomial sub map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMvPolynomialSubMapMem.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMvPolynomialSubMapMem.lean#L43-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMvPolynomialSubMapMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.exists_mvPolynomial_sub_map_mem {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal S) (h : ∀ x : S, ∃ a : R, x - φ a ∈ I) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R,
      p - MvPolynomial.map φ q ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) I := by sorry
