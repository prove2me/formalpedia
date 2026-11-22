-- Prove2me | Theorems.Thm_Nock_NPR_fn_cons_dyck_constraint
-- name    : Nock.NPR.fn_cons_dyck_constraint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:00.511811+00:00
-- url     : https://prove2.me/theorems/da12ac97-0465-42d5-9640-905703790461
-- title:
--   NPR: fn cons dyck constraint
-- statement:
--   **Inverse-free (AIR-constraint) form of the Dyck composition.**  Multiplying
--       `fn_cons_dyck` through by `x` replaces the loose power with fingerprint components —
--       `x·x^{2λL−1} = x^{2λL} = fn₁(l)²` — so every term is a product of components and `x`:
--
--           `x·fn₃(cons(l,r)) = x²·fn₃(l) + fn₁(l)² + x·fn₁(l)²·fn₃(r)`.
--
--       Completeness identity for honest fingerprints (no `x⁻¹` in the statement).  Not a
--       soundness theorem for committed columns; at `x = 0` both sides are 0, so the equation
--       constrains nothing there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L368-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L368-L378

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

theorem Nock.NPR.fn_cons_dyck_constraint (l r : Noun) (x : K) :
    x * (fn (Noun.cell l r) x).2.2
      = x ^ 2 * (fn l x).2.2 + (fn l x).1 ^ 2 + x * (fn l x).1 ^ 2 * (fn r x).2.2 := by sorry
