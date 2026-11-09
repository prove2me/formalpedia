-- Prove2me | Theorems.Thm_MildHamilton_Main_proposition_4_4
-- name    : MildHamilton.Main.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:53:52.873692+00:00
-- url     : https://prove2.me/theorems/92622881-2ccb-4439-bc7d-4ee682ca94ca
-- title:
--   Proposition 4.4, p. 8 — basic Hamilton routers are Hamilton routers
-- statement:
--   Every (directed) graph constructed as in Definition 4.3 is an $A,B$-Hamilton-router.
--
--   Together with Lemma 4.5 this reduces finding a router to finding comparators and connecting paths. The paper cites the statement from Bowtell, Montgomery, Müyesser and Pokrovskiy.
--
--   Differences from the source:
--   - generalization: a graph S consisting exactly of the pieces of Definition 4.3 → any edge relation r containing the pieces; reason: taking r to be the edge relation of S gives the printed statement, and the proof of Lemma 4.7 uses r = H.Adj
--   - generalization: single edges at the boundary (v_{3,1}v_{4,1} and the last column) → paths of any length there; reason: a single edge is the path of length 1; p. 11 states that such subdivisions do not affect the proof of Proposition 4.4
--   - encoding: a 4 × n grid with n left implicit, pieces added to it → n ≥ 1, and pieces meeting the rest of the construction only in their own grid terminals; reason: the boundary edges name column 1, and "add a graph on these terminals" means new vertices otherwise
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Proposition 4.4, p. 8, citing [BMMP26]

import Mathlib
import Definitions.Def_MildHamilton_Main_Router

namespace MildHamilton.Main

/-- Proposition 4.4 (Muyesser, STOC 2027 submission #233, p. 8, from [BMMP26]): every (directed) graph
constructed as in Definition 4.3 is an `A, B`-Hamilton-router. -/
theorem proposition_4_4 {V : Type*} [DecidableEq V] (r : V → V → Prop) (n : ℕ)
    (W A B : Finset V) (h : IsBasicHamiltonRouter r n W A B) :
    IsHamiltonRouter r W A B := by sorry

end MildHamilton.Main
