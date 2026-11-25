-- Prove2me | Theorems.Thm_LocBasisPlaceWork_core
-- name    : LocBasisPlaceWork.core
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:34.581192+00:00
-- url     : https://prove2.me/theorems/96b494af-5f58-45ff-bd4a-a7a9538a2805
-- title:
--   Loc Basis Place Work: core
-- statement:
--   The Loc Basis Place Work construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/SpanClear.lean#L32-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/SpanClear.lean#L32-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open LocBasisPlaceWork

theorem LocBasisPlaceWork.core {R A K : Type*} [CommRing R] [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing A K] (M : Submonoid R) [IsLocalization M A] (N : ℕ)
    (L : Submodule R (Fin N → K)) (hL : L.FG)
    (hsp : Submodule.span K (L : Set (Fin N → K)) = ⊤) :
    ∃ P : Matrix (Fin N) (Fin N) K, P.det ≠ 0 ∧ (∀ a, ∃ s ∈ M, s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s ∈ M, ∃ c : Fin N → R, s • x = ∑ a, c a • P.transpose a := by sorry
