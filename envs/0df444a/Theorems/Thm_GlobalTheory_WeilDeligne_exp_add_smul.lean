-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_exp_add_smul
-- name    : GlobalTheory.WeilDeligne.exp_add_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:37.323049+00:00
-- url     : https://prove2.me/theorems/bfddfd16-e341-48fd-b93a-d0ceff67ee43
-- title:
--   Weil Deligne: exp add smul
-- statement:
--   The Weil Deligne construction uses the exp add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open IsNilpotent
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem GlobalTheory.WeilDeligne.exp_add_smul {N : Matrix n n K} (hN : IsNilpotent N) (s t : K) :
    exp ((s + t) • N) = exp (s • N) * exp (t • N) := by sorry
