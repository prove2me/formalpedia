-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_11
-- name    : ImprovedMMS.Additive.lemma_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:20.836543+00:00
-- url     : https://prove2.me/theorems/50bbb32b-3fa8-4f5f-9279-edae2361cf81
-- title:
--   Lemma 3.11, p. 20 — the representation graph G_C of a cycle-envy-free set is a DAG
-- statement:
--   Let $C$ be a cycle-envy-free set of semi-satisfied agents (each $a_i\in C$ holds $f_i\ne\emptyset$ and $g_i=\emptyset$). Then the representation graph $G_C$, with an edge $v_i\to v_j$ whenever $a_i\in C$ envies $a_j\in C$, is a directed acyclic graph: no vertex $v_i$ lies on a directed cycle,
--   $$\neg\big(v_i\to^{+} v_i\big)\qquad\text{for every } i .$$
--
--   Acyclicity is what makes the topological ordering of Definition 3.12 exist.
--
--   **Formalization Note** "$v_i\to^+v_i$" is `Relation.TransGen` of the edge relation of $G_C$. Envy is between distinct agents (see the definitions), so $G_C$ has no self-loops.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 20, Lemma 3.11 (Definitions 3.9, 3.10, p. 19–20)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Envy

namespace ImprovedMMS.Additive

/-- Lemma 3.11 (p. 20): for every cycle-envy-free set `C` of semi-satisfied agents (bundles
`f_i, g_i`), the representation digraph `G_C` is acyclic: no vertex reaches itself by a directed
path of envy edges. -/
theorem lemma_3_11 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (f g : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, IsSemiSatisfied f g i) (hcef : IsCycleEnvyFree v f C) :
    ∀ i : Fin n, ¬ Relation.TransGen (envyGraph v f C) i i := by sorry

end ImprovedMMS.Additive
