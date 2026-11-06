-- Prove2me | Theorems.Thm_FreeCode_stTiedThree
-- name    : FreeCode.stTiedThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:28.437195+00:00
-- url     : https://prove2.me/theorems/52512933-92e4-4580-87dd-18bb82389d29
-- title:
--   Free Code: st Tied Three
-- statement:
--   **«Theorem 2 gives s_3 = 0»**, for the code that does not depend on k, tied to the machine of
--   Theorem 2 in its decision form behind the reader: the statement `FreeCode.StTiedThree`. In the proof
--   the named machine has the exponent δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L60-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L60-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_FreeCode_Tied
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat

theorem FreeCode.stTiedThree : StTiedThree := by sorry
