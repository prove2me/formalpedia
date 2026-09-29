-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_answered_mem_acc
-- name    : HarelTarjan.PointerLB.answered_mem_acc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:39:40.794528+00:00
-- url     : https://prove2.me/theorems/aacc5814-20f8-4419-a37f-509fc3e7cad7
-- title:
--   Proof of Theorem 1 (p. 340) — a query answered in $k$ steps reaches only nodes accessible in $k$ steps
-- statement:
--   Consider a list structure in which every node has two pointer fields. Let $a, b$ be the input nodes of a query and $c$ a node. If the query with answer $c$ can be answered in $k$ steps, that is, some run of at most $k$ pointer-following steps from $a, b$ holds a pointer to $c$, then
--   $$c \in \mathrm{acc}_k(a) \cup \mathrm{acc}_k(b),$$
--   where $\mathrm{acc}_k(a)$ is the set of nodes accessible from $a$ in $k$ steps or less.
--
--   Contrapositively, a node accessible from neither input in $k$ steps cannot be returned in $k$ steps. This is the step from the machine to accessibility in the proof of Theorem 1: "w would be accessible from neither x nor y in k steps, and an nca query on x and y would be unanswerable in k steps."
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, proof of Theorem 1, first paragraph, last sentence

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem answered_mem_acc {N : Type*} (ptr : N → Fin 2 → Option N) (a b target : N) (k : ℕ)
    (hans : AnsweredIn ptr a b target k) :
    target ∈ acc ptr k a ∪ acc ptr k b := by sorry

end HarelTarjan.PointerLB
