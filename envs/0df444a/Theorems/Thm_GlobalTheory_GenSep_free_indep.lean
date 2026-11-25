-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_free_indep
-- name    : GlobalTheory.GenSep.free_indep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:46.631042+00:00
-- url     : https://prove2.me/theorems/801cf370-0c81-54c2-a782-7cabea5f5cd4
-- title:
--   Gen Sep: free indep
-- statement:
--   The Gen Sep construction uses the free indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L81-L96

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

theorem GlobalTheory.GenSep.free_indep (htr : Algebra.trdeg K Ω = D) (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    {F : Type} [Field F] [Algebra Ω F] (w : AddValuation F (WithTop ℤ)) (u : Fin (D + 1) × Fin N → F)
    (hu : ∀ p, u p ∈ vRing w)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ ((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * algebraMap Ω F (x k) = 0)
    (hint : ∀ k, x k / x j0 ∈ ((vRing w).comap (algebraMap Ω F)).toSubring) :
    letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω F)
    AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω F)))
      (fun s : Free D N j0 => residue (vRing w) ⟨u s.1, hu s.1⟩) := by sorry
