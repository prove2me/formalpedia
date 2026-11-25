-- Prove2me | Theorems.Thm_FractionalColouring_IsFracClique_sum_le
-- name    : FractionalColouring.IsFracClique.sum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:59.825707+00:00
-- url     : https://prove2.me/theorems/1ceef6f0-f373-50d4-86fb-31e7942be66e
-- title:
--   Is Frac Clique: sum le
-- statement:
--   **Weak duality.** A fractional clique weighs at most any fractional colouring.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L114-L118
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L114-L118

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

theorem FractionalColouring.IsFracClique.sum_le {g : V → ℝ} (hg : IsFracClique G g) {x : Finset V → ℝ}
    (hx : IsFracColouring G x) : ∑ v, g v ≤ ∑ s, x s := by sorry
