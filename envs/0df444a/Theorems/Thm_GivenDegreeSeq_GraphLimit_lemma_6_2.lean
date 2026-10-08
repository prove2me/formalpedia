-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_lemma_6_2
-- name    : GivenDegreeSeq.GraphLimit.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:10.824517+00:00
-- url     : https://prove2.me/theorems/6e5f677e-8807-4405-91c3-b7aaf1f38357
-- title:
--   Lemma 6.2 — $P(G\text{ has degree sequence }\mathbf d)\ge\tfrac12\exp(\log(\delta)\,n^{3/2+\varepsilon})$ (sign corrected)
-- statement:
--   Fix $0<\delta<\tfrac12$ and $\varepsilon>0$. There is $N$, depending only on $\delta$ and $\varepsilon$, such that the following holds for every $n\ge N$. Let $\mathbf d=(d_1,\dots,d_n)$ be a valid degree sequence of a simple graph on $n$ vertices, and let $(p_{ij})$ be a symmetric matrix with
--   $$\delta\le p_{ij}\le 1-\delta\quad(i\ne j),\qquad d_i=\sum_{j\ne i}p_{ij}\quad(1\le i\le n).$$
--   Let $G$ be the random graph on $n$ vertices in which each pair $\{i,j\}$ is an edge with probability $p_{ij}$, independently. Then
--   $$\mathbb P(G\text{ has degree sequence }\mathbf d)\ \ge\ \tfrac12\exp\!\big(\log(\delta)\,n^{3/2+\varepsilon}\big)=\tfrac12\,\delta^{\,n^{3/2+\varepsilon}}.$$
--
--   This local lower bound is $e^{-o(n^2)}$, so conditioning an independent-edge model on its degree sequence costs less than the $e^{-cn^2}$ concentration of Lemma 6.1; that comparison drives the proof of Theorem 1.1.
--
--   **Formalization Note** The paper prints $\tfrac12\exp(-\log(\delta)\,n^{(3/2)+\varepsilon})$, which exceeds $1$ because $\log\delta<0$; the intended bound, confirmed by the end of the proof (probability at least $\delta^{|V||B|}$ for a configuration, $|B|=n^{1/2+\varepsilon}$) and by its use on p. 34 ($e^{-C_2n^{7/4}}$), is stated here. "Large enough $n$" is read as $n\ge N(\delta,\varepsilon)$ uniformly in $\mathbf d$ and $p$, as p. 34 uses it. The diagonal entries $p_{ii}$ play no role.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 26, Lemma 6.2 (setting stated just before it on p. 26)

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic
import Definitions.Def_GivenDegreeSeq_GraphLimit_EdgeModel

namespace GivenDegreeSeq.GraphLimit

/-- **Lemma 6.2** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, p. 26), with the sign of the
exponent corrected. Fix `0 < δ < 1/2` and `ε > 0`. There is `N` (depending only on `δ` and `ε`)
such that for every `n ≥ N`, every valid degree sequence `d` on `n` vertices and every symmetric
matrix `(p_ij)` with `δ ≤ p_ij ≤ 1 − δ` for `i ≠ j` and `d_i = Σ_{j ≠ i} p_ij` for all `i`, the
random graph with independent edges of probabilities `p_ij` has degree sequence `d` with
probability at least `½ exp(log(δ) n^{3/2+ε}) = ½ δ^{n^{3/2+ε}}`.
(The paper prints `½ exp(−log(δ) n^{(3/2)+ε})`, which exceeds `1`.) -/
theorem lemma_6_2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (d : Fin n → ℕ) (p : Fin n → Fin n → ℝ),
      GivenDegreeSeq.Interior.IsGraphic d → (∀ i j, p i j = p j i) →
      (∀ i j, i ≠ j → δ ≤ p i j ∧ p i j ≤ 1 - δ) →
      (∀ i, (d i : ℝ) = ∑ j ∈ Finset.univ.erase i, p i j) →
        ENNReal.ofReal (1 / 2 * Real.exp (Real.log δ * (n : ℝ) ^ ((3 : ℝ) / 2 + ε))) ≤
          edgeModel p (withDegrees d) := by sorry

end GivenDegreeSeq.GraphLimit
