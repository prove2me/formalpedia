-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_5_12
-- name    : ImplicitParityWL.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:26.409534+00:00
-- url     : https://prove2.me/theorems/2f50cf1b-13ea-478f-b4ce-142d163e84e9
-- title:
--   Lemma 5.12 — the maps (14)–(16) are an isomorphism on color classes
-- statement:
--   For every seed description on a set $\mathcal A$ of colors, the maps (14)–(16) together give an isomorphism between the subgraphs induced by those color classes in $G_0$ and $G_1$.
--
--   These are the bijections Duplicator announces, and the lemma says that her matches form partial isomorphisms.
--
--   **Formalization Note** The isomorphism is a bijection between the vertices of $G_0$ and of $G_1$ with color in $\mathcal A$, given on vertex names by the maps (14)–(16), preserving colors and preserving adjacency in both directions.
--
--   Differences from the source:
--   - encoding: partial seeds z_v ∈ 𝔽₂^{I_v}, α : Var(𝒜) → 𝔽₂ and masks x_{e,1}, …, x_{e,k+2} → total functions (`SeedData`, α on all variables), of which only those values are read; reason: the same seed descriptions
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 5.12, p.33

import Mathlib
import Definitions.Def_ImplicitParityWL_SeedDescription

namespace ImplicitParityWL

/-- **Lemma 5.12** (Bijections on color classes; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.33): for every seed description on a set `A` of colors, the maps
(14)–(16) together give an isomorphism between the subgraphs induced by those color classes in `G₀` and `G₁`.

**Formalization Note** `|A| ≤ k + 1` is part of Definition 5.10. The isomorphism is a bijection `f` between the vertices
with color in `A`, given on names by the maps (14)–(16), preserving colors and preserving adjacency in both directions. -/
theorem lemma_5_12 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    (I : ImplicitSystem k ℓ W E) (A : Finset (CColor k ℓ W E)) (hA : A.card ≤ k + 1)
    (α : W × Address k ℓ → ZMod 2) (D : SeedData k ℓ W E) (hD : I.IsSeedDescription A α D) :
    ∃ f : {p : I.Vertex 0 // p.val.color ∈ A} ≃ {q : I.Vertex 1 // q.val.color ∈ A},
      (∀ p, (f p).val.val = I.seedMap D p.val.val) ∧
      (∀ p, (f p).val.val.color = p.val.val.color) ∧
      (∀ p p', (I.graph 0).graph.Adj p.val p'.val ↔ (I.graph 1).graph.Adj (f p).val (f p').val) := by sorry

end ImplicitParityWL
