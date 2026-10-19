-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_bijective
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_bijective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T11:58:25.926842+00:00
-- url     : https://prove2.me/theorems/9a704310-1684-4b91-886a-039cbda361f8
-- title:
--   Finite packet shear matrices are invertible
-- statement:
--   Let there be finitely many packets, let S be any finite set of monomial exponents in variables X₀,…,Xₘ, and let each δᵢ be an arbitrary complex univariate formal power series. Form the coefficient matrix on S of the substitution fixing X₀ and sending Xᵢ₊₁ to Xᵢ₊₁+δᵢ(X₀), acting separately on each packet. Then
--
--   $$E_\delta:\mathbb C^{\{0,\ldots,K-1\}\times S}\longrightarrow\mathbb C^{\{0,\ldots,K-1\}\times S}$$
--
--   is bijective. No positivity, vanishing-order, or closure condition on S is required. Empty exponent sets and zero packets are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_bijective
    {m : ℕ} (K : ℕ) (S : Finset (Fin (m + 1) → ℕ))
    (delta : Fin m → PowerSeries ℂ) :
    Function.Bijective (finitePacketShearMatrix K S delta).mulVecLin := by sorry
