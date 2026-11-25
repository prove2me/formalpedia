-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_exists_adapted
-- name    : GlobalTheory.GenSep.exists_adapted
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:40.682547+00:00
-- url     : https://prove2.me/theorems/ed5e4baf-851d-5514-b009-104f026b12de
-- title:
--   Gen Sep: exists adapted
-- statement:
--   The Gen Sep construction uses the exists adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L280-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L280-L292

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

theorem GlobalTheory.GenSep.exists_adapted (x : Fin N → Ω) (hx : ∃ k, x k ≠ 0) (v : AddValuation Ω (WithTop ℤ)) :
    ∃ j0, x j0 ≠ 0 ∧ ∀ k, 0 ≤ v (x k / x j0) := by sorry
