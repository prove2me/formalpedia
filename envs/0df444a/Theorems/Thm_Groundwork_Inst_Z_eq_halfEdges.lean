-- Prove2me | Theorems.Thm_Groundwork_Inst_Z_eq_halfEdges
-- name    : Groundwork.Inst.Z_eq_halfEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:50.010733+00:00
-- url     : https://prove2.me/theorems/93e4285c-84a2-4fa3-800b-fc57ccff67db
-- title:
--   Inst: Z eq half Edges
-- statement:
--   Half-edges: every edge is cut into two half-edges that must agree.
--   Z(R) = Σ_ℓ ∏_w R_w(ℓ(w,·)) ∏_{w<w'} [ℓ(w,w') = ℓ(w',w)], with ℓ(w,w) = d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L182-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L182-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}

theorem Groundwork.Inst.Z_eq_halfEdges [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = ∑ ℓ ∈ Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset A)) d,
      (∏ w, R w (ℓ w)) * ∏ p ∈ pairs J, if ℓ p.1 p.2 = ℓ p.2 p.1 then 1 else 0 := by sorry
