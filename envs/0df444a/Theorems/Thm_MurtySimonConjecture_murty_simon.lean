-- Prove2me | Theorems.Thm_MurtySimonConjecture_murty_simon
-- name    : MurtySimonConjecture.murty_simon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:22:04.810429+00:00
-- url     : https://prove2.me/theorems/f0cc733a-8275-4085-b892-d623306ffe59
-- title:
--   Murty Simon Conjecture: murty simon
-- statement:
--   **The Murty–Simon conjecture** (Das–Fox, Theorem 1.1): a diameter-2-critical graph on `n`
--   vertices has at most `⌊n²/4⌋` edges.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L65-L67
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L65-L67

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}

theorem MurtySimonConjecture.murty_simon [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) : #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by sorry
