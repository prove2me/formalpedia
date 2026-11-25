-- Prove2me | Theorems.Thm_FractionalColouring_isFracClique_mycielskiClique
-- name    : FractionalColouring.isFracClique_mycielskiClique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:26.958994+00:00
-- url     : https://prove2.me/theorems/8bcdd4c5-86b2-5de9-82a2-373d5d06b370
-- title:
--   Fractional Colouring: is Frac Clique mycielski Clique
-- statement:
--   The Fractional Colouring construction uses the is Frac Clique mycielski Clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L248-L315
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L248-L315

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.isFracClique_mycielskiClique {g : V → ℝ} (hg : IsFracClique G g) {a : ℝ} (ha : 1 ≤ a)
    (hga : ∀ x, IsFracColouring G x → ∀ (T : Finset V) (c : ℝ), 0 ≤ c →
      (∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c) →
        ∑ v ∈ T, g v ≤ c * a) :
    IsFracClique (graph G) (mycielskiClique g a) := by sorry
