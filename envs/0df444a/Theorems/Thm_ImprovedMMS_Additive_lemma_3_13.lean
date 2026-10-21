-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_13
-- name    : ImprovedMMS.Additive.lemma_3_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:25.628401+00:00
-- url     : https://prove2.me/theorems/c9806432-c48a-4892-9e86-13626a6f3e4e
-- title:
--   Lemma 3.13, p. 20 — winner, loser and unsaturated-vertex conditions for an MCMWM
-- statement:
--   Let $H$ be a weighted bipartite graph with sides $\hat{\mathcal X}$, $\hat{\mathcal Y}$ and weights $w$, and let $M=\{(\hat x_1,\hat y_1),\dots,(\hat x_k,\hat y_k)\}$ be an MCMWM of $H$. Let $T\subseteq\{\hat y_1,\dots,\hat y_k\}$ be non-empty, and let $M(T)$ be the set of vertices matched by $M$ to the vertices of $T$. Then:
--
--   1. some $\hat y_j\in T$ is a **winner** in $T$: $w(\hat x_j,\hat y_j)\ge w(\hat x_i,\hat y_j)$ for all $\hat x_i\in M(T)$ with $(\hat x_i,\hat y_j)\in E(H)$;
--   2. some $\hat y_j\in T$ is a **loser** in $T$: $w(\hat x_i,\hat y_i)\ge w(\hat x_j,\hat y_i)$ for all $\hat y_i\in T$ with $(\hat x_j,\hat y_i)\in E(H)$;
--   3. for any $\hat y_i\in T$ and any vertex $\hat x_j\in\hat{\mathcal X}$ unsaturated by $M$ with $(\hat x_j,\hat y_i)\in E(H)$,
--   $$w(\hat x_i,\hat y_i)\ \ge\ w(\hat x_j,\hat y_i).$$
--
--   Applied to the value graph, it shows that assigning goods by an MCMWM produces a cycle-envy-free set of semi-satisfied agents.
--
--   **Formalization Note** $\hat x_i$ denotes the mate of $\hat y_i$, written `(xi, yi) ∈ Mt`. The page says "for every subset $T$"; (i) and (ii) assert the existence of a vertex of $T$ and fail for $T=\emptyset$, so $T$ is non-empty (condition (iii) holds for every $T$). The three conditions are stated as one conjunction.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 20, Lemma 3.13 (MCMWM, p. 20)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

namespace ImprovedMMS.Additive

/-- Lemma 3.13 (p. 20): let `Mt` be an MCMWM of the weighted bipartite graph with sides `X`, `Y`,
edges `E ⊆ X × Y` and weights `w`, and let `T` be a non-empty set of `Y`-vertices saturated by
`Mt` (the mate of `y` is the `x` with `(x, y) ∈ Mt`). Then
(i) some `y_j ∈ T` is a winner: `w(x_j, y_j) ≥ w(x_i, y_j)` for every mate `x_i` of a vertex of
`T` with `(x_i, y_j) ∈ E`;
(ii) some `y_j ∈ T` is a loser: `w(x_i, y_i) ≥ w(x_j, y_i)` for every `y_i ∈ T` with
`(x_j, y_i) ∈ E`;
(iii) `w(x_i, y_i) ≥ w(x_j, y_i)` for every `y_i ∈ T` and every unsaturated `x_j ∈ X` with
`(x_j, y_i) ∈ E`. -/
theorem lemma_3_13 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y) (w : α → β → ℝ)
    (Mt : Finset (α × β)) (hM : IsMCMWM E w Mt)
    (T : Finset β) (hT : T ⊆ Mt.image Prod.snd) (hTne : T.Nonempty) :
    (∃ yj ∈ T, ∀ xj : α, (xj, yj) ∈ Mt → ∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt →
        (xi, yj) ∈ E → w xi yj ≤ w xj yj) ∧
    (∃ yj ∈ T, ∀ xj : α, (xj, yj) ∈ Mt → ∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt →
        (xj, yi) ∈ E → w xj yi ≤ w xi yi) ∧
    (∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt → ∀ xj ∈ X, (∀ y : β, (xj, y) ∉ Mt) →
        (xj, yi) ∈ E → w xj yi ≤ w xi yi) := by sorry

end ImprovedMMS.Additive
