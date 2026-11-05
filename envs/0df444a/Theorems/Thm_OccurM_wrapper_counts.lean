-- Prove2me | Theorems.Thm_OccurM_wrapper_counts
-- name    : OccurM.wrapper_counts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:43:15.297751+00:00
-- url     : https://prove2.me/theorems/68d378a6-0208-4172-9b89-cf3fd0933e59
-- title:
--   Occur M: wrapper counts
-- statement:
--   For any coding `code` by nonempty words and any `pre` that numbers the variables that occur:
--   every wrapper counts within the printed bound, with the constant `stepsC q (2·C + 1)`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L33-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L33-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_OccurM_Wrapper
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)

theorem OccurM.wrapper_counts {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (code : ∀ (_ : ℕ) {V : ℕ}, CNF V → List Bool) {pre : List Bool → List Bool}
    (hpre : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
      SatK.numSat ψ = numSatOcc φ ∧ pre (code k φ) = SatM.enc k ψ)
    (hlen : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ (code k φ).length)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : SatM.CountsTM M (SatM.bound (SatM.rPow α) C))
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre id N q) :
    ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
      Nonempty (TM2OutputsInTime N.tm ((code k φ).map N.inputAlphabet.invFun) (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map N.outputAlphabet.invFun))
        (timeClauses α (stepsC q (2 * C + 1)) k φ.length + stepsC q (2 * C + 1) * (code k φ).length ^ stepsC q (2 * C + 1))) := by sorry
