-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_OverGauss_approx
-- name    : GlobalTheory.GenSep.OverGauss.approx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:15.935463+00:00
-- url     : https://prove2.me/theorems/642d5bfe-4feb-5845-bd40-dd8d784f1978
-- title:
--   Over Gauss: approx
-- statement:
--   The Over Gauss construction uses the approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L348-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L348-L375

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

theorem GlobalTheory.GenSep.OverGauss.approx (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) {ϖ : la.adicCompletionIntegers K}
    (hϖ : ϖ ∈ maximalIdeal (la.adicCompletionIntegers K)) (n : ℤ) {c : la.adicCompletion K} {a : K}
    {o : la.adicCompletionIntegers K}
    (hc : c - algebraMap K (la.adicCompletion K) a = ((ϖ ^ n.natAbs : la.adicCompletionIntegers K) : la.adicCompletion K) * o) :
    (n : WithTop ℤ) ≤ w (e (κ c) - ι (algebraMap K Ω a)) := by sorry
