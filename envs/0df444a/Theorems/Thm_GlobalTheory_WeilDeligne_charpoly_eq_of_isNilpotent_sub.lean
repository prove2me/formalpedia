-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_charpoly_eq_of_isNilpotent_sub
-- name    : GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:34.46797+00:00
-- url     : https://prove2.me/theorems/7289a42f-5e78-5888-86f2-e00fd7300487
-- title:
--   Weil Deligne: charpoly eq of is Nilpotent sub
-- statement:
--   The Weil Deligne construction uses the charpoly eq of is Nilpotent sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L64-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L64-L85

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

theorem GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f g : End K V} (hc : Commute f g)
    (hn : IsNilpotent (g - f)) : f.charpoly = g.charpoly := by sorry
