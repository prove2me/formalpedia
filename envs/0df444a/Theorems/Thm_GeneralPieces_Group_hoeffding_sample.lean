-- Prove2me | Theorems.Thm_GeneralPieces_Group_hoeffding_sample
-- name    : GeneralPieces.Group.hoeffding_sample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:09.939656+00:00
-- url     : https://prove2.me/theorems/d461ecbf-3158-45f8-a4b6-ed3ac8b5e579
-- title:
--   Group: hoeffding sample
-- statement:
--   "The sum S of a uniformly random set of j entries of a list of numbers in [0, R] satisfies Pr(S
--   ≥ E S + ζjR) ≤ exp(−2jζ²)." Here E S is j times the mean of the list. The text cites this; the
--   proof is `ClauseBound.Group.card_sample_tail_le`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L59-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L59-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}

theorem GeneralPieces.Group.hoeffding_sample {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ R)
    (hs : s.Nonempty) (j : ℕ) (hζ : 0 ≤ ζ) :
    (#{S ∈ powersetCard j s | j * ((∑ i ∈ s, x i) / #s) + ζ * j * R ≤ ∑ i ∈ S, x i} : ℝ) ≤ Real.exp (-(2 * j * ζ ^ 2)) * #(powersetCard j s) := by sorry
