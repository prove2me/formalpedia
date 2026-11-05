-- Prove2me | Theorems.Thm_GeneralPieces_wfe_mono
-- name    : GeneralPieces.wfe_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:40.900344+00:00
-- url     : https://prove2.me/theorems/17a7919f-e16e-4b2d-aaa3-49c46797f146
-- title:
--   General Pieces: wfe mono
-- statement:
--   An instance whose entries are at most 2^B in absolute value has entries at most 2^{B'} for every
--   B' ≥ B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L251-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L251-L252

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
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group

theorem GeneralPieces.wfe_mono {K lam B B' : ℕ} {J : PInst} (h : WFe K lam B J) (hB : B ≤ B') : WFe K lam B' J := by sorry
