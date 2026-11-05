-- Prove2me | Theorems.Thm_GeneralPieces_Top_val_caseI
-- name    : GeneralPieces.Top.val_caseI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:19.220644+00:00
-- url     : https://prove2.me/theorems/bc22ef20-aeef-4d50-b0ad-de59580acf94
-- title:
--   Top: val case I
-- statement:
--   A network on g = 3K⁸ nodes, rebalanced to K nodes by case (i) of Lemma 8 and handed to a correct
--   algorithm for cliques, gives its value, if β, the string length of the clique handed on, is at
--   least the lemma's L and the length of the padding string `pad` is at least each of the five powers
--   `f1`–`f5`, which bound the work.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L72-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L72-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat

theorem GeneralPieces.Top.val_caseI {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hS : S.Correct ok) {C : Type} (F : FNet C) (c : C) (pad : U) (i : Idx)
    (N : Network (Fin (3 * S.K i ^ 8)) (List Bool) (List Bool)) (P B β : ℕ) (hi : ok i) (hK : 2 ≤ S.K i)
    (hN : F.toP.Presents c N 0 0) (hSz : N.Sized P B) (hβ : AppRunningTime.Lof (S.K i) (3 * S.K i ^ 8) (1 / (2 * (S.K i : ℝ))) P N.U ≤ β) (hβ1 : 1 ≤ β)
    (f1 : S.K i ^ (3 * S.K i ^ 8) ≤ pad.length) (f2 : 2 ^ (P * (2 * (3 * S.K i ^ 8) / S.K i)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((S.K i - 1) * β) ≤ pad.length)
    (f5 : 2 ^ S.need (i, List.replicate β (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ()) ≤ pad.length) :
    ((rebalG pad (S.K i) (3 * S.K i ^ 8) β F c).elim 0 fun I => S.run (pad, i, I)) = N.value := by sorry
