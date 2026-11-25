-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_gauss_one
-- name    : GlobalTheory.GenSep.gauss_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:45.983468+00:00
-- url     : https://prove2.me/theorems/6f208015-aae4-5b6d-b4a6-3f2475531014
-- title:
--   Gen Sep: gauss one
-- statement:
--   The Gen Sep construction uses the gauss one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L100-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L100-L133

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
set_option maxHeartbeats 1000000

theorem GlobalTheory.GenSep.gauss_one (htr : Algebra.trdeg K Ω = D) (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    {F : Type} [Field F] (w : AddValuation F (WithTop ℤ)) (ι : Ω →+* F) (u : Fin (D + 1) × Fin N → F)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔ ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 ≤ w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * ι (x k) = 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι u P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι u P) = w (ι ((aeval (subst x j0) P).coeff α)) := by sorry
