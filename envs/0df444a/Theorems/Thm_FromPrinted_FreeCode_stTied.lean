-- Prove2me | Theorems.Thm_FromPrinted_FreeCode_stTied
-- name    : FromPrinted.FreeCode.stTied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:17:03.110192+00:00
-- url     : https://prove2.me/theorems/daff04bf-cbbe-4d20-a6c3-a4a0a605ad30
-- title:
--   Free Code: st Tied
-- statement:
--   **Corollary 5, tied to the reduction**, for the code that does not depend on k: for every k ≥ 3
--   and δ > 0 there are a polynomial-time reader of the code, τ, ℓ₃ and τ₃ such that the reduction
--   (sparsify at width k with the threshold parameter τ, split every long clause, ask `core3 ℓ₃ τ₃`)
--   behind the reader itself has polynomial-time steps and decides k-SAT with the exponent δ, a Turing
--   machine with finite alphabets simulates it with polynomial overhead, and that Turing machine decides
--   k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `FromPrinted.FreeCode.StTied`. With ε = (δ/2)/3
--   the tree at width k has at most 2^{εn} leaves of at most B·n clauses; the machine of Theorem 2 in
--   its decision form is taken with the exponent δ₃ = ε/(1 + (k−3)·B). In the proof the named machine
--   has the exponent δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/FreeCode.lean#L67-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/FreeCode.lean#L67-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Tied
import Definitions.Def_FreeCode_Main
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic
import Definitions.Def_FromPrinted_FreeCode
import Theorems.Thm_FreeCode_stTied
import Theorems.Thm_SplitSat_endFrom
import Theorems.Thm_SplitSat_eth_and_seth_false
import Theorems.Thm_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_stTiedTM
import Theorems.Thm_SplitSat_stTiedThreeTM

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode SatFree
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement stSATsplit stTiedTM stTiedThreeTM endFrom eth_and_seth_false
open FromPrinted.SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.FreeCode

theorem FromPrinted.FreeCode.stTied : StTied := by sorry
