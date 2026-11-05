-- Prove2me | Theorems.Thm_GeneralPieces_grouping_general
-- name    : GeneralPieces.grouping_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:38.449898+00:00
-- url     : https://prove2.me/theorems/4dc10762-243e-41af-9a55-4cbe1d744dfc
-- title:
--   General Pieces: grouping general
-- statement:
--   Lemma 8 in the form in which the recursion and the top levels call it: in case (i) or (ii), for
--   every label length β ≥ L (in the recursion "the number L depends on ι";
--   the programs use one label length for all ι, an upper bound), `rebalG` returns the (K, β)-clique
--   with the value of the network. Two bounds hold for its entries: the paper's B' = ⌈2gP/K⌉ + g²B, and
--   P·G + B·(G + G²)·K with G = ⌊2g/K⌋, which is the smaller one once 4g/K + 2 < g and is the one that
--   the programs compute with. In place of P ≥ 1 only β ≥ 1 is needed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L260-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L260-L276

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group

theorem GeneralPieces.grouping_general (C : Type) (F : FNet C) (x : C) (K g : ℕ) (ζ : ℝ) (N : Network (Fin g) (List Bool) (List Bool)) (P B β : ℕ) (pad : U)
    (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hN : F.toP.Presents x N 0 0) (hS : N.Sized P B) (hcase : AppRunningTime.Cases K g ζ P N.c)
    (hβ : AppRunningTime.Lof K g ζ P N.U ≤ β) (hβ1 : 1 ≤ β) (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F x = some J ∧ zval K J = N.value ∧
      WFe K β (min (AppRunningTime.B'of K g P B) (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K)) J := by sorry
