-- Prove2me | Theorems.Thm_MassDataIdxRed_glRed_coe
-- name    : MassDataIdxRed.glRed_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:58.888642+00:00
-- url     : https://prove2.me/theorems/231d6249-7de6-4d2c-a0e4-7a403701ad72
-- title:
--   Mass Data Idx Red: gl Red coe
-- statement:
--   The Mass Data Idx Red construction uses the gl Red coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GlRedEqOneIff.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GlRedEqOneIff.lean#L24-L25

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

theorem MassDataIdxRed.glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := by sorry
