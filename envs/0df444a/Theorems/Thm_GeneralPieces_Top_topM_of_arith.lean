-- Prove2me | Theorems.Thm_GeneralPieces_Top_topM_of_arith
-- name    : GeneralPieces.Top.topM_of_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:43.297848+00:00
-- url     : https://prove2.me/theorems/f70252fd-885b-429d-9f94-c39a3ee5c144
-- title:
--   Top: top M of arith
-- statement:
--   The padding machine, run on the function and the exponent function of a solver with a sequence
--   of indices, computes that function and counts within C·2^(C·k·m·r(m)) steps. The inequality from the
--   proof of Theorem A(c), that the exponent at the level picked for m is
--   O(k·m·e_ℓ), is the hypothesis `hA`, for this sequence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/EndM.lean#L31-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/EndM.lean#L31-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Definitions.Def_GeneralPieces_Top_EndM
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End

theorem GeneralPieces.Top.topM_of_arith (hP : CountKSatRate.StPaddedW) (hC : StCorrectM) (hK : StCertM) {Idx : Type} [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ)
    (Q : S.Seq e C₀) (hA : ∃ A : ℕ, ∀ k m : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 9 ≤ m → (needTop S (Q.pick (root9 m)).2 k m : ℝ) ≤ A * k * m * e (Q.pick (root9 m)).1.length)
    (hS : S.Poly) (r : ℕ → ℝ) (c₁ : ℕ) (hr : ∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ r m)
    (he : ∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * r m) : Tied.TopM S Q.pick r := by sorry
