-- Prove2me | Theorems.Thm_FreeCode_stTied
-- name    : FreeCode.stTied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:58.622523+00:00
-- url     : https://prove2.me/theorems/e22e9f58-b69e-42d5-8549-587def367fe3
-- title:
--   Free Code: st Tied
-- statement:
--   **Corollary 5, tied to the reduction**, for the code that does not depend on k: the statement
--   `FreeCode.StTied`. With ε = (δ/2)/3 the tree at width k has at most 2^{εn} leaves of at most B·n
--   clauses; the machine of Theorem 2 in its decision form is taken with the exponent δ₃ = ε/(1 +
--   (k−3)·B). In the proof the named machine has the exponent δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L69-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L69-L82

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

theorem FreeCode.stTied : StTied := by sorry
