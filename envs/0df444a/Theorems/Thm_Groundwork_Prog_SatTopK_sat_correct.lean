-- Prove2me | Theorems.Thm_Groundwork_Prog_SatTopK_sat_correct
-- name    : Groundwork.Prog.SatTopK.sat_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:11.7835+00:00
-- url     : https://prove2.me/theorems/052224bc-4aba-4d72-8b33-2cc23020c0bd
-- title:
--   Sat Top K: sat correct
-- statement:
--   Let `step`, `root` sparsify width k with at most 2^{δn/3} leaves of at most Bl·n clauses, let
--   `dec` decode, and let M return, on m clauses of ≤ k
--   literals, within A·2^{δ'm} steps (δ'·Bl ≤ δ/3) and size A·(size φ)^A, an integer that is positive
--   iff φ is satisfiable. Then `satMK dec step root M`
--   decides every encoded k-CNF on n variables within c·2^{δn} steps and within size polynomial in the
--   length of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L102-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L102-L265

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_WidthK_Top_Sat
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

theorem Groundwork.Prog.SatTopK.sat_correct {k : ℕ} (hk : 1 ≤ k) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    {dec : List Bool → ℕ × Fml} {step : Fml → Option (Fml × Fml)} {root : Fml → Fml} {Dd Bl Sk : ℕ}
    (hdec : ∀ (n : ℕ) (φ : Sat3.CNF n), (∀ C ∈ φ, C.length ≤ k) → dec (SatK.enc k φ) = (n, Decode.toN φ))
    (hsp : Sparsifies k (δ / 3) step root Dd Bl Sk) (hδB : δ' * Bl ≤ δ / 3) (M : Stepped Fml ℤ) (A : ℕ)
    (hM : ∀ φ : Fml, (∀ C ∈ φ, C.length ≤ k) →
      ∃ (T : ℕ) (v : ℤ), M.Runs φ T (A * size φ ^ A) v ∧ (0 < v ↔ φ.Sat) ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * φ.length)) :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
      ∃ (T : ℕ) (b : Bool), (satMK dec step root M).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) b ∧
        (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by sorry
