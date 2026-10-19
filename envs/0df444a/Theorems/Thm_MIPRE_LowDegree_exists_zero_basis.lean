-- Prove2me | Theorems.Thm_MIPRE_LowDegree_exists_zero_basis
-- name    : MIPRE.LowDegree.exists_zero_basis
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:24:33.264842+00:00
-- url     : https://prove2.me/theorems/daa254fd-334b-490e-90dc-93b2ac79d0f2
-- title:
--   Boolean-cube zero basis, with individual-degree bounds on every certificate
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.ZeroBasis` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Certificates for polynomials vanishing on the Boolean cube. The paper's `prop:zero-basis`, used in classical PCP completeness. Reduction by `X i * (1 - X i)` preserves every individual-degree bound. This is stronger than the total-degree bound in the general combinatorial Nullstellensatz.
--
--   **Boolean-cube zero basis**, with individual-degree bounds on every certificate.
--   The equality is an identity of polynomials, not only an equality of functions.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F : Type*} [Field F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.exists_zero_basis (f : MvPolynomial (Fin m) F) {d : ℕ}
--       (hd : ∀ i, f.degreeOf i ≤ d) (hf : ∀ y : Fin m → Bool, eval (pt y) f = 0) :
--       ∃ c : Fin m → MvPolynomial (Fin m) F,
--         f = ∑ i, c i * cubeZero i ∧ ∀ i j, (c i).degreeOf j ≤ d
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.exists_zero_basis` is declared in `MIPRE/Foundations/LowDegree/ZeroBasis.lean`, lines 139–164. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/ZeroBasis.lean#L139-L164; blueprint lem:pcp-zero-basis

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.LowDegree.exists_zero_basis (f : MvPolynomial (Fin m) F) {d : ℕ}
    (hd : ∀ i, f.degreeOf i ≤ d) (hf : ∀ y : Fin m → Bool, eval (pt y) f = 0) :
    ∃ c : Fin m → MvPolynomial (Fin m) F,
      f = ∑ i, c i * cubeZero i ∧ ∀ i j, (c i).degreeOf j ≤ d := by sorry
