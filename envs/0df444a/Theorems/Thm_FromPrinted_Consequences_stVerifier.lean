-- Prove2me | Theorems.Thm_FromPrinted_Consequences_stVerifier
-- name    : FromPrinted.Consequences.stVerifier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:06.182467+00:00
-- url     : https://prove2.me/theorems/ea297522-0f32-4b0d-8b19-643eadd66136
-- title:
--   Consequences: st Verifier
-- statement:
--   **The verifier for tautologies, with the machine named**: for every k ≥ 3 and δ > 0 there are τ,
--   ℓ₃, τ₃, c such that `SATsplit k τ ℓ₃ τ₃` has polynomial-time steps and decides k-SAT with the
--   exponent δ and the constant c, and the verifier made from it has polynomial-time steps and, on every
--   witness w and the code of a k-DNF ψ on n variables, ends within c·2^{δn} steps, on states of size at
--   most c·(length of the code + 1)^c, with the bit that says whether ψ is a tautology.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L45-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
import Definitions.Def_FromPrinted_Verifier
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences

theorem FromPrinted.Consequences.stVerifier : StVerifier := by sorry
