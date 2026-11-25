-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_OverGauss_gauss
-- name    : GlobalTheory.GenSep.OverGauss.gauss
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:24.687243+00:00
-- url     : https://prove2.me/theorems/18ff57fe-3c8f-5d0e-8973-1f3d5fd317f5
-- title:
--   Over Gauss: gauss
-- statement:
--   The Over Gauss construction uses the gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L333-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L333-L346

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

theorem GlobalTheory.GenSep.OverGauss.gauss (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o)) (htr : Algebra.trdeg K Ω = D)
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (j0 : Fin N) (hx : x j0 ≠ 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι (fun p => e (φ (X p))) P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι (fun p => e (φ (X p))) P) = w (ι ((aeval (subst x j0) P).coeff α)) := by sorry
