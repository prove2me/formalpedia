-- Prove2me | Theorems.Thm_MIPRE_LowDegree_card_filter_ker_mul_prime
-- name    : MIPRE.LowDegree.card_filter_ker_mul_prime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:03.555584+00:00
-- url     : https://prove2.me/theorems/caf50aaa-31b3-4e4d-b45c-9847056f7439
-- title:
--   A nonzero 𝔽-linear functional on a finite 𝔽-vector space has kernel of index |𝔽|. Every fibre is a translate of the kernel, and there are |𝔽| of them
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.Anticomm` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). When is a Pauli-test question tuple anticommuting?. The Pauli basis test samples `ω = (u_X, u_Z, r_X, r_Z)` and the two Pauli operators it asks about commute or anticommute according to whether `γ(ω) = tr_{q → 2} \bigl( (r_X · ind_m(u_X)) · (r_Z · ind_m(u_Z)) \bigr)` vanishes. The paper's `fact:omega-anticomm-prob` says each case has probability at least `(1 - 3md/q)/2`; this file is that fact. `ind_m(x) ∈ 𝔽_q^{2^m}` is the vector of the subcube indicator polynomials of `MIPRE/Foundations/LowDegree/Encoding.lean` evaluated at an *arbitrary* point `x`, and the dot product of two of them is one…
--
--   **A nonzero `𝔽`-linear functional on a finite `𝔽`-vector space has kernel of index `|𝔽|`.**
--   Every fibre is a translate of the kernel, and there are `|𝔽|` of them.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
--
--   theorem MIPRE.LowDegree.card_filter_ker_mul_prime (τ : V →ₗ[F] F) (hτ : τ ≠ 0) :
--       #{r ∈ (univ : Finset V) | τ r = 0} * Fintype.card F = Fintype.card V
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.card_filter_ker_mul_prime` is declared in `MIPRE/Foundations/LowDegree/Anticomm.lean`, lines 116–139. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository (there named `MIPRE.LowDegree.card_filter_ker_mul'`; renamed for the platform, which requires ASCII identifiers). The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/Anticomm.lean#L116-L139; blueprint def:generalized-pauli

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
  [Fintype V] [DecidableEq V]
omit [DecidableEq V]

theorem MIPRE.LowDegree.card_filter_ker_mul_prime (τ : V →ₗ[F] F) (hτ : τ ≠ 0) :
    #{r ∈ (univ : Finset V) | τ r = 0} * Fintype.card F = Fintype.card V := by sorry
