-- Prove2me | Theorems.Thm_OccurM_after_front
-- name    : OccurM.after_front
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:09.844073+00:00
-- url     : https://prove2.me/theorems/4a4d0a9c-35ff-433b-aa97-c2f64d4e2ff8
-- title:
--   Occur M: after front
-- statement:
--   For any coding `code` by nonempty words and any polynomial-time `front` that maps the code of
--   (k, φ) to `SatM.enc k (ren φ)`: five statements, which for the compact code with `rencC` are the
--   five fields of `TopOccur`, and for the code with N in unary with `renc` those of
--   `TopOccurUnary`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L67-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L67-L98

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}

theorem OccurM.after_front (h0 : 0 ≤ α) (h1 : α ≤ 1) (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow α))
    (code : ∀ (_ : ℕ) {N : ℕ}, CNF N → List Bool) {front : List Bool → List Bool} (hfront : PolyT front)
    (hcode : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → front (code k φ) = SatM.enc k (ren φ))
    (hlen : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ (code k φ).length) :
    PolyT (fun p : List Bool × U => AM S pick (front p.1, p.2)) ∧ PolyT (fun x => eM S pick (front x)) ∧
    (∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eM S pick (front (code k φ)) ≤ pad.length →
      AM S pick (front (code k φ), pad) = SatK.binary (numOcc φ) (numSatOcc φ)) ∧
    (∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (eM S pick (front (code k φ)) : ℝ) ≤ G * expClauses α k φ.length) ∧
    ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((AM S pick (front x, pad (eM S pick (front x)))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ eM S pick (front x) + 1) ^ q))) ∧
      ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
        Nonempty (TM2OutputsInTime M.tm ((code k φ).map M.inputAlphabet.invFun)
          (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map M.outputAlphabet.invFun)) (timeClauses α C k φ.length + C * (code k φ).length ^ C)) := by sorry
