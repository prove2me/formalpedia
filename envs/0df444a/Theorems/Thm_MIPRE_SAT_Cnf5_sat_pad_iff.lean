-- Prove2me | Theorems.Thm_MIPRE_SAT_Cnf5_sat_pad_iff
-- name    : MIPRE.SAT.Cnf5.sat_pad_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:12.404781+00:00
-- url     : https://prove2.me/theorems/cd31f5c4-9390-424d-bdb4-a2908bf71dd6
-- title:
--   Padding satisfaction is exactly original satisfaction and both complete blank tails
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Padding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding decoupled descriptions. The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`. The original clauses are embedded in the larger five blocks. Additional clauses force both answer tails to be blank tapes; the three auxiliary tails are free. In particular, the conclusion preserves `Circuit.DescribesDecider`, which specifies every answer bit, rather than merely preserving the accepted answer prefixes. The circuit construction and its running time are separate obligations.
--
--   Padding satisfaction is exactly original satisfaction and both complete blank tails.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Cnf5
--
--   theorem MIPRE.SAT.Cnf5.sat_pad_iff {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
--       (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
--         (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
--       (a b : Fin (2 ^ ℓ') → Bool) (w₁ w₂ w₃ : Fin (2 ^ r') → Bool) :
--       (pad hℓ hr φ).Sat a b w₁ w₂ w₃ ↔
--         φ.Sat (a ∘ blockInclusion hℓ) (b ∘ blockInclusion hℓ)
--           (w₁ ∘ blockInclusion hr) (w₂ ∘ blockInclusion hr) (w₃ ∘ blockInclusion hr) ∧
--         (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → a i = decide ((i : ℕ) % 2 = 0)) ∧
--         (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → b i = decide ((i : ℕ) % 2 = 0))
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Cnf5.sat_pad_iff` is declared in `MIPRE/Foundations/SAT/Padding.lean`, lines 75–103. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Padding.lean#L75-L103; blueprint lem:pcp-padding-semantics

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_SAT_Padding

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Cnf5

theorem MIPRE.SAT.Cnf5.sat_pad_iff {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
    (a b : Fin (2 ^ ℓ') → Bool) (w₁ w₂ w₃ : Fin (2 ^ r') → Bool) :
    (pad hℓ hr φ).Sat a b w₁ w₂ w₃ ↔
      φ.Sat (a ∘ blockInclusion hℓ) (b ∘ blockInclusion hℓ)
        (w₁ ∘ blockInclusion hr) (w₂ ∘ blockInclusion hr) (w₃ ∘ blockInclusion hr) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → a i = decide ((i : ℕ) % 2 = 0)) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → b i = decide ((i : ℕ) % 2 = 0)) := by sorry
