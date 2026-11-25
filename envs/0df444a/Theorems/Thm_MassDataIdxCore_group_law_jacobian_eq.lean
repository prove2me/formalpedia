-- Prove2me | Theorems.Thm_MassDataIdxCore_group_law_jacobian_eq
-- name    : MassDataIdxCore.group_law_jacobian_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:51.483368+00:00
-- url     : https://prove2.me/theorems/1f2e6069-b6a5-47c9-9263-f245b00c6976
-- title:
--   Mass Data Idx Core: group law jacobian eq
-- statement:
--   The Mass Data Idx Core construction uses the group law jacobian eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L49-L54

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

theorem MassDataIdxCore.group_law_jacobian_eq (J : Matrix n n T) (hJ : Formalism.UG.cT s J = J) : J.map (t2 θ) = (J.map (t1 θ))ᵀ := by sorry
