-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_OverGauss_eval_eq
-- name    : GlobalTheory.GenSep.OverGauss.eval_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:29.136109+00:00
-- url     : https://prove2.me/theorems/88088eca-f517-5b0e-a702-db9271f31919
-- title:
--   Over Gauss: eval eq
-- statement:
--   The Over Gauss construction uses the eval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L321-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L321-L331

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

theorem GlobalTheory.GenSep.OverGauss.eval_eq (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K)) :
    eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun p => e (φ (X p))) P =
      e (φ (MvPolynomial.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) P)) := by sorry
