-- Prove2me | Theorems.Thm_GeneralPieces_Descend_descend_state2
-- name    : GeneralPieces.Descend.descend_state2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:57.735454+00:00
-- url     : https://prove2.me/theorems/e8c43b6f-e9aa-47ed-ae7b-01ae2c2b5ac1
-- title:
--   Descend: descend state2
-- statement:
--   The steps of the schedule, applied to any state that is in order: the factor is multiplied by
--   some q ≥ 1, and the sum plus the results of brute force on the work list at the end is q times
--   the sum plus the values Z of the work list at the start.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Descend.lean#L35-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Descend.lean#L35-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Alg_Descend
import Definitions.Def_GeneralPieces_Rec_Descend
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists ClauseBound.Alg ClauseBound.Alg.Descend

theorem GeneralPieces.Descend.descend_state2 (P : PiecesF) (hX : StExpandG2 P) {pad : U} {K₀ : ℕ} : ∀ (sched : List Step) {Kup lam B cnt z : ℕ} (st fin : DState),
    ChainG2 P K₀ Kup lam sched → FitsG P pad.length Kup lam B cnt z sched → st.2.1.length = lam → st.2.2.length ≤ cnt →
    (∀ I ∈ st.2.2, WFe Kup lam B I) → st.1.1.natAbs < 2 ^ z → st.1.2 < 2 ^ z →
    sched.foldl (fun st s => cap pad ((0, 1), [], []) (stepG P pad st s)) st = fin →
    ∃ c : ℕ, 1 ≤ c ∧ fin.1.2 = c * st.1.2 ∧
      fin.1.1 + (fin.2.2.map (bruteF pad K₀)).sum = c * (st.1.1 + (st.2.2.map (zval Kup)).sum)
  := by sorry
