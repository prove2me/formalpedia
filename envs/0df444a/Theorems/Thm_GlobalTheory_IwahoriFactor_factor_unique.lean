-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_factor_unique
-- name    : GlobalTheory.IwahoriFactor.factor_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:26:35.400431+00:00
-- url     : https://prove2.me/theorems/e0a62200-bb77-41f2-b138-a10e7741dc53
-- title:
--   Iwahori Factor: factor unique
-- statement:
--   The Iwahori Factor construction uses the factor unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L97-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L97-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}

theorem GlobalTheory.IwahoriFactor.factor_unique {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by sorry
