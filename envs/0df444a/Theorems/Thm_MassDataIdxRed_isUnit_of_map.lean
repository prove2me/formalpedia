-- Prove2me | Theorems.Thm_MassDataIdxRed_isUnit_of_map
-- name    : MassDataIdxRed.isUnit_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:32.571496+00:00
-- url     : https://prove2.me/theorems/67d4db8f-e146-4f9d-8fb1-2ec9026fff19
-- title:
--   Mass Data Idx Red: is Unit of map
-- statement:
--   The Mass Data Idx Red construction uses the is Unit of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GlRedEqOneIff.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GlRedEqOneIff.lean#L9-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxRed
open Matrix

theorem MassDataIdxRed.isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by sorry
