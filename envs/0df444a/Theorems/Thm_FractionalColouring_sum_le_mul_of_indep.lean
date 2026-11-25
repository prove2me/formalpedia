-- Prove2me | Theorems.Thm_FractionalColouring_sum_le_mul_of_indep
-- name    : FractionalColouring.sum_le_mul_of_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:13.193854+00:00
-- url     : https://prove2.me/theorems/72615048-80b6-4194-8677-c44420912a0a
-- title:
--   Fractional Colouring: sum le mul of indep
-- statement:
--   **Local weak duality.** If every independent set meets `T` in `g`-weight at most `c`, then
--   `g(T) ≤ c · w(x)` for every fractional colouring `x`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L99-L111
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L99-L111

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.sum_le_mul_of_indep {g : V → ℝ} (hg : ∀ v, 0 ≤ g v) {T : Finset V} {c : ℝ}
    (hc : ∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c)
    {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    ∑ v ∈ T, g v ≤ c * ∑ s, x s := by sorry
