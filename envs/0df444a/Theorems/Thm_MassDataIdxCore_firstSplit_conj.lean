-- Prove2me | Theorems.Thm_MassDataIdxCore_firstSplit_conj
-- name    : MassDataIdxCore.firstSplit_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:20.243805+00:00
-- url     : https://prove2.me/theorems/1147b7df-6fe4-4bba-9a60-c67a58d0c57e
-- title:
--   Mass Data Idx Core: first Split conj
-- statement:
--   The Mass Data Idx Core construction uses the first Split conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap)
include hs

theorem MassDataIdxCore.firstSplit_conj (t : T) : t1 θ (s t) = t2 θ t := by sorry
