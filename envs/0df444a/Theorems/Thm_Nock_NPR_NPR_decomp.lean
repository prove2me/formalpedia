-- Prove2me | Theorems.Thm_Nock_NPR_NPR_decomp
-- name    : Nock.NPR.NPR_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:54.70993+00:00
-- url     : https://prove2.me/theorems/180ed4ee-82eb-493a-858e-33b0a7d2e05e
-- title:
--   NPR: NPR decomp
-- statement:
--   **`Lem:NPR_decomp` (main.tex:1218).**  The three algebraic identities characterizing
--       `cons`.  We state the paper's `↔ n = cons(nL,nR)` as `Φ n = Φ (cons nL nR)` — *field-noun*
--       equality: `Φ n = Φ n'` is equality of the pair (leaf-count, leaf polynomial, Dyck polynomial),
--       i.e. of the `(dyck word, 𝔽-valued leaf array)`, which is the paper's notion of noun equality
--       over `𝔽` (the paper's nouns are field-valued, `main.tex:347–349`, `1023`).  (Structural
--       `n = cell nL nR` implies it via `congrArg`, `NPR_decomp_of_cons`; the converse to *structural*
--       `Nat` equality does NOT hold — distinct `Nat` leaves congruent mod the characteristic give the
--       same field-noun (compiled counterexample `RedTeam.Batch5.b5_npr_decomp_field_not_structural`
--       over `ZMod 5`), the "same field-noun"
--       phenomenon also underlying `collision_card_le`.  This module does not prove `Φ` injective on
--       field-nouns; that is the paper's ion property, whose soundness error is bounded by
--       `collision_prob_le`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L279-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L279-L296

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]

theorem Nock.NPR.NPR_decomp (n nL nR : Noun) :
    Φ (K := K) n = Φ (K := K) (Noun.cell nL nR)
      ↔ ( (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
        ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
        ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
            + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 ) := by sorry
