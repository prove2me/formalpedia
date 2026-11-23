-- Prove2me | Theorems.Thm_GlobalTheory_isSymplecticBasisOfType_standardAltForm
-- name    : GlobalTheory.isSymplecticBasisOfType_standardAltForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:03.660901+00:00
-- url     : https://prove2.me/theorems/95c9798b-3546-4173-b10e-41e5dda88d21
-- title:
--   Global Theory: is Symplectic Basis Of Type standard Alt Form
-- statement:
--   The Global Theory construction uses the is Symplectic Basis Of Type standard Alt Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L44-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.isSymplecticBasisOfType_standardAltForm [Fintype ι] [DecidableEq ι] (d : ι → R) :
    IsSymplecticBasisOfType (standardAltForm d) (Pi.basisFun R (ι ⊕ ι)) d := by sorry
