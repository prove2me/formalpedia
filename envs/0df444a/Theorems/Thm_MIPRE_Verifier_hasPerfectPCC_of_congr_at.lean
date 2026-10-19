-- Prove2me | Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_congr_at
-- name    : MIPRE.Verifier.hasPerfectPCC_of_congr_at
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:10.383985+00:00
-- url     : https://prove2.me/theorems/fc8c0e0d-86b5-441a-bc61-efb42d9ee63c
-- title:
--   Perfect PCC strategies also depend only on the game at the current index
-- statement:
--   A statement of the module `MIPRE.Foundations.VerifierIndexTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Verifier transport at a single index. Wrappers may change a sampler at exceptional indices. Equality of its dimension and CL presentations at the index in question suffices to preserve both quantum value and perfect PCC strategies; the programs need not agree elsewhere.
--
--   Perfect PCC strategies also depend only on the game at the current index.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Verifier
--   open MIPRE.CL
--   variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
--
--   theorem MIPRE.Verifier.hasPerfectPCC_of_congr_at (h : SamplerAgreement V W n)
--       (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
--       (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T
--   ```
--
--   **Formalization Note** `MIPRE.Verifier.hasPerfectPCC_of_congr_at` is declared in `MIPRE/Foundations/VerifierIndexTransport.lean`, lines 71–93. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/VerifierIndexTransport.lean#L71-L93

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
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_VerifierIndexTransport

open MIPRE
open MIPRE.Verifier
open MIPRE.CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}

theorem MIPRE.Verifier.hasPerfectPCC_of_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by sorry
