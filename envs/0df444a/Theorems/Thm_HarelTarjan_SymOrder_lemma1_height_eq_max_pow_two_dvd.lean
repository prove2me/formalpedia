-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_lemma1_height_eq_max_pow_two_dvd
-- name    : HarelTarjan.SymOrder.lemma1_height_eq_max_pow_two_dvd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:46:23.724283+00:00
-- url     : https://prove2.me/theorems/8ea2cab3-069c-49f1-8f8e-9563121f6c34
-- title:
--   Lemma 1 — the height of $v$ is the largest $h$ with $2^h \mid \mathrm{sym}(v)$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. The height $h(v)$ of a vertex $v$ is the largest integer $h$ such that $2^h$ divides $\mathrm{sym}(v)$:
--   $$2^{h(v)} \mid \mathrm{sym}(v) \quad\text{and}\quad 2^{h(v)+1} \nmid \mathrm{sym}(v).$$
--
--   Lemma 1 lets the height of a vertex be read off its number, the 2-adic valuation of $\mathrm{sym}(v)$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, Lemma 1

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- Lemma 1 (p. 342): the height of a vertex `v` is the largest integer `h` such that `2^h`
divides `sym(v)`. -/
theorem lemma1_height_eq_max_pow_two_dvd {d : ℕ} (v : Vertex d) :
    2 ^ height v ∣ sym v ∧ ¬ 2 ^ (height v + 1) ∣ sym v := by sorry

end HarelTarjan.SymOrder
