-- Prove2me | Theorems.Thm_GeneralPieces_Group_group_uniform
-- name    : GeneralPieces.Group.group_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:14.02405+00:00
-- url     : https://prove2.me/theorems/14bc8f4d-4adf-4817-b9d9-5d84168653d6
-- title:
--   Group: group uniform
-- statement:
--   "Then each G_γ is a uniformly random set of g/K nodes": if at most the fraction ε of all sets of
--   n nodes have a property, then for at most the fraction ε of all permutations e the group γ of χ₀∘e
--   has it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L45-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean#L45-L52

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

theorem GeneralPieces.Group.group_uniform (γ : Fin K) (Q : Finset (Fin (K * n)) → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{A ∈ powersetCard n (univ : Finset (Fin (K * n))) | Q A} : ℝ) ≤ ε * #(powersetCard n (univ : Finset (Fin (K * n))))) :
    (#{e : Equiv.Perm (Fin (K * n)) | Q (cls e γ)} : ℝ) ≤ ε * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by sorry
