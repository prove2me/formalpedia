-- Prove2me | Theorems.Thm_MurtySimon_lemma_3_2
-- name    : MurtySimon.lemma_3_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:20.43433+00:00
-- url     : https://prove2.me/theorems/58cde361-a355-59e6-9d24-38484464574f
-- title:
--   Murty Simon: lemma 3 2
-- statement:
--   **Lemma 3.2.** In an equality case every component of `𝓘` with a vertex in `E ∪ F_c` is
--   left-lopsided, and every matching uses at most one of its left vertices.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L150-L185
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L150-L185

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.lemma_3_2 (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : 1 ≤ cA G ∅ C + cB G ∅ C) :
    cA G ∅ C = cB G ∅ C + 1 ∧
      ∀ N, IsEdgeMatching G N → #((LC0 C).filter (· ∈ N)) ≤ 1 := by sorry
