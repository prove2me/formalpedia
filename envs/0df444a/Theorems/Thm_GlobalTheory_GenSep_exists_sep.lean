-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_exists_sep
-- name    : GlobalTheory.GenSep.exists_sep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:21:57.52367+00:00
-- url     : https://prove2.me/theorems/8fa847a4-4ed1-4c6b-b520-66bb956666ce
-- title:
--   Gen Sep: exists sep
-- statement:
--   The Gen Sep construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L424-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L424-L442

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

theorem GlobalTheory.GenSep.exists_sep (v v' : AddValuation Ω (WithTop ℤ)) (h : ∃ a, v a = 1) (h' : ∃ a, v' a = 1) (hne : v ≠ v') :
    ∃ a, 0 < v a ∧ 0 < v' (a - 1) := by sorry
