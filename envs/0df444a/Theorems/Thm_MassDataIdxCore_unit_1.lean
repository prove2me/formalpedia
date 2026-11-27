-- Prove2me | Theorems.Thm_MassDataIdxCore_unit_1
-- name    : MassDataIdxCore.unit_1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:40.995819+00:00
-- url     : https://prove2.me/theorems/32ffe9c8-9996-461b-916c-72e883e8091f
-- title:
--   Mass Data Idx Core: unit 1
-- statement:
--   The Mass Data Idx Core construction uses the unit 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L31-L38

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
variable {n : Type} [Fintype n] [DecidableEq n]

theorem MassDataIdxCore.unit_1 (J : Matrix n n T) (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((g : Matrix n n T).map (t2 θ))ᵀ * J.map (t1 θ) * (g : Matrix n n T).map (t1 θ) = J.map (t1 θ) := by sorry
