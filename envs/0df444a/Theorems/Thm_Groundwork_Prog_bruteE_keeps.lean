-- Prove2me | Theorems.Thm_Groundwork_Prog_bruteE_keeps
-- name    : Groundwork.Prog.bruteE_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:56:02.64007+00:00
-- url     : https://prove2.me/theorems/3f3edb23-36c3-4c62-be97-da9f3fee24b3
-- title:
--   Prog: brute E keeps
-- statement:
--   The brute-force evaluator `bruteE K` keeps `IsPolyT`: applied to an `IsPolyT` machine for the
--   tensors it gives one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Brute.lean#L63-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Brute.lean#L63-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_ToTuring_Poly_Brute
set_option autoImplicit false
section
section
open Groundwork
open Stepped
open Groundwork.Prog

theorem Groundwork.Prog.bruteE_keeps (K : ℕ) : (bruteE K).Keeps := by sorry
