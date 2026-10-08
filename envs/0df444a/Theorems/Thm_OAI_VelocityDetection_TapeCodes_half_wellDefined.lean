-- Prove2me | Theorems.Thm_OAI_VelocityDetection_TapeCodes_half_wellDefined
-- name    : OAI.VelocityDetection.TapeCodes.half_wellDefined
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.857134+00:00
-- url     : https://prove2.me/theorems/80ed4dcd-862a-4b78-93ad-82d13c0d91c4
-- statement:
--   The theorem states that, for a base b that is a positive natural number (with N also a positive natural number, though it plays no role in the statement), the numerical value of a digit list is unchanged by appending blanks. Here a word is a list of digits in Fin b, and word(w) is the natural number obtained by reading w as base-b digits with the first entry as the least significant digit, that is, the sum of w_i b^i. The relation BlankExtends(a,c) is Mathlib's Turing-machine notion that c is obtained from a by appending finitely many copies of the default symbol of Fin b, which is the digit 0. The claim is that for all digit lists a and c in Fin b, if BlankExtends(a,c) holds then word(a) = word(c), so the encoding is well defined on tapes up to trailing blanks.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NavierStokesVelocity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NavierStokesVelocity.lean; bytes 15447..15515
-- Kind: theorem; definition proof obligation extracted; recipe navier_stokes_half_well_defined recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_NavierStokesVelocity

namespace OAI

noncomputable section

namespace VelocityDetection.TapeCodes

open scoped BigOperators Topology ContDiff

open Set Function Filter

open Set Function Filter MeasureTheory

open scoped Topology BigOperators ContDiff

open scoped Topology ContDiff BigOperators

open scoped Topology ContDiff ZeroAtInfty

open scoped Topology ContDiff ZeroAtInfty BigOperators

open scoped Topology

open Turing Stacks

variable {b N : ℕ} [NeZero b] [NeZero N]

theorem half_wellDefined :
    ∀ a c : List (Fin b), BlankExtends a c → word a = word c := by
  sorry

end VelocityDetection.TapeCodes
end
end OAI
