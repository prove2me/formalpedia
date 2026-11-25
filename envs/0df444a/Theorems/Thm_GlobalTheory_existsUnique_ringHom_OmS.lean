-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_ringHom_OmS
-- name    : GlobalTheory.existsUnique_ringHom_OmS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:03.349675+00:00
-- url     : https://prove2.me/theorems/79ebdccd-199c-4680-bb6d-821f47282c37
-- title:
--   Global Theory: exists Unique ring Hom Om S
-- statement:
--   The Global Theory construction uses the exists Unique ring Hom Om S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/AlgebraicIndependentFreeVar.lean#L25-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/AlgebraicIndependentFreeVar.lean#L25-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_AlgebraicIndependentFreeVar
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
open MvPolynomial
open NumberField
open scoped TensorProduct
open MvPolynomial

theorem GlobalTheory.existsUnique_ringHom_OmS :
    ∀ (K Ω L : Type) [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (D N : ℕ)
      (j₀ : Fin (N + 1)) (x : Fin N → Ω) (τ : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N → L) (φ : Ω →ₐ[K] L),
      Algebra.trdeg K Ω = D → AlgebraicIndependent K τ →
      (∀ i : Fin D, τ (i.succ, j₀) + ∑ k, τ (i.succ, j₀.succAbove k) * φ (x k) = 0) →
      ∃! P : _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* L, (∀ a : Ω, P (algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = φ a) ∧
        ∀ p, P (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j₀ x p) = τ p := by sorry
