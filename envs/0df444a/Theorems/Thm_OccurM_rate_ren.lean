-- Prove2me | Theorems.Thm_OccurM_rate_ren
-- name    : OccurM.rate_ren
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:37.104019+00:00
-- url     : https://prove2.me/theorems/0b190312-c906-467e-9617-6386905b35b9
-- title:
--   Occur M: rate ren
-- statement:
--   The exponent of the top level at the renamed formula is at most G·km/(log m)^α, with the G of
--   `TopM.rate`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L54-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L54-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_OccurM_Prep
import Definitions.Def_OccurM_Arith
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_OccurM_Top
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}

theorem OccurM.rate_ren (h0 : 0 ≤ α) {G : ℕ}
    (hG : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * SatM.rPow α φ.length))
    {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hm : 2 ≤ φ.length) (hφ : SatK.IsKCNF k φ) :
    (eM S pick (SatM.enc k (ren φ)) : ℝ) ≤ G * expClauses α k φ.length := by sorry
