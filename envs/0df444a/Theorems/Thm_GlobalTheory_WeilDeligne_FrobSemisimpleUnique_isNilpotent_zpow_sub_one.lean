-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_FrobSemisimpleUnique_isNilpotent_zpow_sub_one
-- name    : GlobalTheory.WeilDeligne.FrobSemisimpleUnique.isNilpotent_zpow_sub_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:01:56.340954+00:00
-- url     : https://prove2.me/theorems/a3504904-d1e6-501e-94aa-0854257e77d2
-- title:
--   Frob Semisimple Unique: is Nilpotent zpow sub one
-- statement:
--   The Frob Semisimple Unique construction uses the is Nilpotent zpow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNilpotentZpowSubOne.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNilpotentZpowSubOne.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem GlobalTheory.WeilDeligne.FrobSemisimpleUnique.isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by sorry
