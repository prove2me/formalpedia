-- Prove2me | Theorems.Thm_GeneralPieces_DefGenPieces_sum_min_words
-- name    : GeneralPieces.DefGenPieces.sum_min_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:05.542863+00:00
-- url     : https://prove2.me/theorems/dcd1c84a-9ada-4a9d-a7b2-4bbb2f6c604f
-- title:
--   Def Gen Pieces: sum min words
-- statement:
--   Σ_θ [w = θ]·G(θ) = G(w) over the words of 2λ bits, and nothing changes over shorter words: a sum
--   t·b over the words of c₀ bits with the value V = G(w) is also the sum over the words of
--   min(c₀, 2λ) bits of the two functions that are [w = θ] and G on words of 2λ bits and t and b on all
--   others.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L38-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L38-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces
open Trim

theorem GeneralPieces.DefGenPieces.sum_min_words {lam c₀ : ℕ} {w : List Bool} (hw : w.length = 2 * lam) (t b G : List Bool → ℤ) {V : ℤ} (h1 : V = ∑ θ ∈ words c₀, t θ * b θ) (h2 : G w = V) :
    V = ∑ θ ∈ words (min c₀ (2 * lam)),
      (bif decide (θ.length = 2 * lam) then (if w = θ then 1 else 0) else t θ) * (bif decide (θ.length = 2 * lam) then G θ else b θ) := by sorry
