-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_subst_mem
-- name    : GlobalTheory.GenSep.subst_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:25:35.050332+00:00
-- url     : https://prove2.me/theorems/a8c284ab-7928-4bf2-9de4-14d7021838d3
-- title:
--   Gen Sep: subst mem
-- statement:
--   The Gen Sep construction uses the subst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L43-L49

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
variable {Ω : Type} [Field Ω] {D N : ℕ}

theorem GlobalTheory.GenSep.subst_mem (x : Fin N → Ω) (j0 : Fin N) {W : Subring Ω} (hW : ∀ k, x k / x j0 ∈ W)
    (p : Fin (D + 1) × Fin N) : subst x j0 p ∈ Formalism.L2.Pj.LocAlg.intPoly _ W := by sorry
