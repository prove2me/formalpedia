-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_xo
-- name    : GeneralPieces.GenF.DD_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:37.478464+00:00
-- url     : https://prove2.me/theorems/e4d7de41-b0a6-41e9-8890-d3ab7be8313d
-- title:
--   Gen F: DD xo
-- statement:
--   The Gen F construction uses the DD xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L37-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L37-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.DD_xo (rd : Bool) (n : ℕ) : DD rd (xo rd n) = 0 := by sorry
