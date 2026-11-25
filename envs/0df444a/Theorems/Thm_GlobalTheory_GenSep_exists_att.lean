-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_exists_att
-- name    : GlobalTheory.GenSep.exists_att
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:33.545838+00:00
-- url     : https://prove2.me/theorems/532cfb96-122c-5d54-8e15-6c0036db01bd
-- title:
--   Gen Sep: exists att
-- statement:
--   The Gen Sep construction uses the exists att property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L377-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L377-L422

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)
variable {la φ κ x}

theorem GlobalTheory.GenSep.exists_att (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    (hφ : ∀ c : K', ∃ a b, φ b ≠ 0 ∧ φ b * c = φ a) (htr : Algebra.trdeg K Ω = D) (hx : ∃ k, x k ≠ 0)
    {F F' : Type} [Field F] [Field F'] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    {w' : AddValuation F' (WithTop ℤ)} {ι' : Ω →+* F'} {e' : K' →+* F'}
    (h : OverGauss la φ κ x w ι e) (h' : OverGauss la φ κ x w' ι' e') (heq : ∀ a, w (ι a) = w' (ι' a)) :
    ∃ A : Subring (F × F'), (∀ z ∈ A, Att w w' ι ι' z) ∧ (∀ a, (ι a, ι' a) ∈ A) ∧ (∀ c, (e c, e' c) ∈ A) ∧
      ∀ y y', (y, y') ∈ A → y ≠ 0 → y' ≠ 0 → (y⁻¹, y'⁻¹) ∈ A := by sorry
