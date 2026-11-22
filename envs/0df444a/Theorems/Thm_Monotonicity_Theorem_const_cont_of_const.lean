-- Prove2me | Theorems.Thm_Monotonicity_Theorem_const_cont_of_const
-- name    : Monotonicity_Theorem.const_cont_of_const
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T22:01:33.11262+00:00
-- url     : https://prove2.me/theorems/fe447b60-620b-444b-808f-5f02e8b7d3b4
-- title:
--   Constant maps are continuous
-- statement:
--   A definable map constant on an interval is continuous at every point of it, with the interval itself as the delta window. Used for constant pieces and the constant case of discontinuity-finiteness.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.const_cont_of_const {R : Type} [LinearOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (lo hi : R)
    (hsub : ∀ x : Power R 1, openInterval (Endpoint.finite lo) (Endpoint.finite hi) x → I x)
    (hconst : ∀ x (hxI : I x), openInterval (Endpoint.finite lo) (Endpoint.finite hi) x →
      ∀ y (hyI : I y), openInterval (Endpoint.finite lo) (Endpoint.finite hi) y →
      (f.toFun ⟨x, hxI⟩).1 = (f.toFun ⟨y, hyI⟩).1) :
    (openInterval (Endpoint.finite lo) (Endpoint.finite hi)).Subset
      (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  sorry
