-- Prove2me | Theorems.Thm_FreeCode_tied_of_decidesW
-- name    : FreeCode.tied_of_decidesW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:35.753312+00:00
-- url     : https://prove2.me/theorems/8dcfa3d7-9ac6-42e7-958d-778932e0dbc5
-- title:
--   Free Code: tied of decides W
-- statement:
--   A procedure D with polynomial-time steps that decides w-SAT on (N in unary, formula) with the
--   exponent δ/2, behind the reader `readFree`: there are a Turing machine M with finite alphabets and
--   c, q such that the machine behind the reader has polynomial-time steps and decides w-SAT on codes
--   with the exponent δ and the constant c, M simulates it with polynomial overhead, and M decides w-SAT
--   on codes within ⌊c·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L46-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Tied.lean#L46-L55

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

theorem FreeCode.tied_of_decidesW {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {D : StepMachine (List Unit × Fml) Bool} (hp : PolyTimeSteps D) {c₀ : ℕ} (hD : DecidesW w D (δ / 2) c₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ PolyTimeSteps (Stepped.mapIn readFree D) ∧
      DecidesFree (Stepped.mapIn readFree D) w δ c ∧ Simulates M (Stepped.mapIn readFree D) q ∧ SatFree.DecidesTM w M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
