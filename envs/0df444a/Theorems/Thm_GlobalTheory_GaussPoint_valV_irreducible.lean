-- Prove2me | Theorems.Thm_GlobalTheory_GaussPoint_valV_irreducible
-- name    : GlobalTheory.GaussPoint.valV_irreducible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:39.44847+00:00
-- url     : https://prove2.me/theorems/3a746889-7023-4aee-883e-80ef544430c0
-- title:
--   Gauss Point: val V irreducible
-- statement:
--   The Gauss Point construction uses the val V irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPoint.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPoint.lean#L38-L41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
open GlobalTheory GlobalTheory.GaussPoint
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem GlobalTheory.GaussPoint.valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by sorry
