-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_5
-- name    : MinCostArbPacking.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:19.600204+00:00
-- url     : https://prove2.me/theorems/bbcccd22-1549-4123-bdeb-9fddf5e668d5
-- title:
--   Lemma 4.5 — contraction and lifting
-- statement:
--   **Lemma 4.5 (Contraction and lifting).** Assume the standing assumptions of §4.2. For every set $X$ of arcs crossing the tight blocks of $I$, the following are equivalent:
--
--   1. $I\cup X$ is independent in the original graph;
--   2. $I^{cr}\cup X$ is a union of $k$ forests in the contracted graph.
--
--   The equivalence is unchanged if any internal basis $I[T]$ is replaced by another basis of $E[T]$.
--
--   This reduces the compatibility of a batch of proposals to an independence test in the contracted graph.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ independent, cheapest for its indegree vector, no arc into $r$, indegree $\le k$) → explicit hypotheses `NoLoopNoRootArc` and `Standing`; reason: the source states them once for the whole section; they are hypotheses of every lemma there
--   - encoding: replacing internal bases $I[T]$ by bases of $E[T]$ → any $I_2$ with the same crossing arcs as $I$ and $I_2[T]$ a basis of $E[T]$ for every block $T$; reason: this is exactly a simultaneous replacement of internal bases
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.2, p.12, Lemma 4.5

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.5 (Contraction and lifting), p.12: for every set `X` of arcs crossing the tight blocks of
`I`, `I ∪ X` is independent in `𝒢^k` iff `I^cr ∪ X` is a union of `k` forests in the contracted
graph; and the equivalence is unchanged if the internal bases `I[T]` are replaced by any other bases
of `E[T]`. -/
theorem lemma_4_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (I : Finset E) (hI : G.Standing k r c I) :
    (∀ X : Finset E, (∀ e ∈ X, G.IsCrossing k I e) →
      (G.IndepK k (I ∪ X) ↔ (G.contract k I).IndepK k (G.crossingPart k I ∪ X))) ∧
    (∀ I₂ : Finset E, (∀ e, G.IsCrossing k I e → (e ∈ I₂ ↔ e ∈ I)) →
      (∀ T, G.IsTightBlock k I T → G.IsBasisOf k (G.induced I₂ T) (G.induced Finset.univ T)) →
      ∀ X : Finset E, (∀ e ∈ X, G.IsCrossing k I e) →
        (G.IndepK k (I₂ ∪ X) ↔ (G.contract k I).IndepK k (G.crossingPart k I ∪ X))) := by sorry

end MinCostArbPacking.Main
