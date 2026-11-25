-- Prove2me | Theorems.Thm_GlobalTheory_TracePowCharpoly_newton_multiset
-- name    : GlobalTheory.TracePowCharpoly.newton_multiset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:44.424541+00:00
-- url     : https://prove2.me/theorems/9ba1e034-0a65-48d4-a1e6-852a4de09087
-- title:
--   Trace Pow Charpoly: newton multiset
-- statement:
--   The Trace Pow Charpoly construction uses the newton multiset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEqOfTracePowers.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEqOfTracePowers.lean#L18-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.TracePowCharpoly
open Polynomial Finset

theorem GlobalTheory.TracePowCharpoly.newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by sorry
