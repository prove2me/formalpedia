-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_xi
-- name    : GeneralPieces.GenF.DD_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:28.577643+00:00
-- url     : https://prove2.me/theorems/7effb9f3-6d4f-4b30-aad7-3922eeb115b1
-- title:
--   Gen F: DD xi
-- statement:
--   The Gen F construction uses the DD xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L35-L35

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

theorem GeneralPieces.GenF.DD_xi (rd : Bool) {n : ℕ} (hn : 1 ≤ n) : DD rd (xi rd n) = JmT n := by sorry
