-- Prove2me | Theorems.Thm_MassDataIdxCore_unit_2
-- name    : MassDataIdxCore.unit_2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:32.677953+00:00
-- url     : https://prove2.me/theorems/f4f63840-299e-5b8b-bf15-b75d03205ebc
-- title:
--   Mass Data Idx Core: unit 2
-- statement:
--   The Mass Data Idx Core construction uses the unit 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L40-L47

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

theorem MassDataIdxCore.unit_2 (J : Matrix n n T) (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((g : Matrix n n T).map (t1 θ))ᵀ * J.map (t2 θ) * (g : Matrix n n T).map (t2 θ) = J.map (t2 θ) := by sorry
