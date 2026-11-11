-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_6_5
-- name    : IncApproxVC.Oblivious.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:48.526772+00:00
-- url     : https://prove2.me/theorems/f3ff65bc-e003-4505-b172-29994a62241c
-- title:
--   Lemma 6.5 — an $s$-rooted vertex cut maps to an $s^+$-rooted cut of $G_{\mathrm{split}}$ of size $|S|$ and volume $\le(1+k/\delta)\mathrm{vol}^+_G(L)+1$
-- statement:
--   Let $G=(V,E)$ be a simple directed graph with split graph $G_{\mathrm{split}}$, and fix a root $s\in V$. For every $s$-rooted separation triple $(L,S,R)$ of $G$, the pair
--   $$S'=\{v^-,v^+\mid v\in L\}\cup\{v^-\mid v\in S\},\qquad T'=\{v^-,v^+\mid v\in R\}\cup\{v^+\mid v\in S\}$$
--   is an $s^+$-rooted cut of $G_{\mathrm{split}}$ with
--   $$|\partial^+_{G_{\mathrm{split}}}(S')|=|S|,\qquad \mathrm{vol}^+_{G_{\mathrm{split}}}(S')=\mathrm{vol}^+_G(L)+|L|+|S|.$$
--   Put $k=|S|$. If $k\ge 1$ and the minimum out-degree $\delta$ of $G$ satisfies $\delta\ge 1$, then
--   $$\mathrm{vol}^+_{G_{\mathrm{split}}}(S')\ \le\ \Big(1+\frac{k}{\delta}\Big)\mathrm{vol}^+_G(L)+1.$$
--
--   **Formalization Note.** "$\delta$ is the minimum out-degree" is written as: $\delta\le\deg^+_G(v)$ for all $v$ and $\delta=\deg^+_G(v)$ for some $v$.
--
--   Differences from the source: none.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 21, Lemma 6.5

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace IncApproxVC.Oblivious

/-- **Lemma 6.5** (mapping rooted cuts from the original graph to the split graph), p. 21. For every
`s`-rooted separation triple `(L, S, R)` of `G`, the pair `S′ = {v⁻, v⁺ | v ∈ L} ∪ {v⁻ | v ∈ S}`,
`T′ = {v⁻, v⁺ | v ∈ R} ∪ {v⁺ | v ∈ S}` is an `s⁺`-rooted cut of `G_split` with
`|∂⁺_{G_split}(S′)| = |S|` and `vol⁺_{G_split}(S′) = vol⁺_G(L) + |L| + |S|`. If moreover `k = |S| ≥ 1`
and the minimum out-degree `δ` of `G` is at least `1`, then
`vol⁺_{G_split}(S′) ≤ (1 + k/δ) vol⁺_G(L) + 1`. -/
theorem lemma_6_5 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (s : V) (L S R : Finset V) (hsep : G.IsSeparationTriple L S R) (hs : s ∈ L) :
    (Digraph.IsEdgeCut (L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus)
          (R.image Digraph.minus ∪ R.image Digraph.plus ∪ S.image Digraph.plus) ∧
        Digraph.plus s ∈ L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus) ∧
      (G.split.outBoundary
          (L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus)).card =
        S.card ∧
      G.split.vol (L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus) =
        G.vol L + L.card + S.card ∧
      ∀ δ : ℕ, 1 ≤ S.card → 1 ≤ δ → (∀ v, δ ≤ G.outDeg v) → (∃ v, G.outDeg v = δ) →
        (G.split.vol (L.image Digraph.minus ∪ L.image Digraph.plus ∪
            S.image Digraph.minus) : ℝ) ≤
          (1 + (S.card : ℝ) / δ) * (G.vol L : ℝ) + 1 := by sorry

end IncApproxVC.Oblivious
