-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_8
-- name    : LovaszECCKernel.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:04.489168+00:00
-- url     : https://prove2.me/theorems/46d09175-7061-4f7d-b7da-7ab70c0e6691
-- title:
--   Lemma 8 — large graphs whose second part is not dominant are yes-instances
-- statement:
--   **Lemma 8.** Let $k\ge0$ be an integer and $G$ a finite simple graph on $n$ vertices with at most one universal vertex. Let $M\subseteq\binom{V(G)}{2}$ be such that $G\triangle M$ is complete multipartite with part sizes $t_1\ge t_2\ge\cdots$ (zero beyond the number of non-empty parts) and
--   $$t_2\ \le\ 1.5\,(n-t_1-t_2)+k+4|M|,\qquad n\ \ge\ 300k+150|M| .$$
--   Then $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$.
--
--   With Lemma 4 this covers both outcomes for large graphs near complete multipartite, which is why the kernel's output has $O(k)$ vertices (Algorithm 1, lines 16–25).
--
--   Differences from the source:
--   - encoding: t₁, t₂ of a complete r-partite graph whose parts may be empty → sizes of the non-empty parts in non-increasing order, padded with 0; reason: empty parts have size 0
--   - encoding: t₂ ≤ 1.5·(n − t₁ − t₂) + k + 4|M| → compared in ℝ with n = |V|; reason: the constant 1.5 is not an integer
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 8, p.38 (= PDF p.38)

import Mathlib
import Definitions.Def_LovaszECCKernel_InLb
import Definitions.Def_LovaszECCKernel_flip
import Definitions.Def_LovaszECCKernel_partSize
import Definitions.Def_LovaszECCKernel_universalVertices

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 8** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 8, p.38 (= PDF p.38)): "Let k ≥ 0 be an integer. Let G be an n-vertex
graph with at most one universal vertex, and let M ⊆ (V(G) choose 2) be such that G△M is complete
r-partite with t2 ≤ 1.5 · (n − t1 − t2) + k + 4|M| and n ≥ 300k + 150|M|. Then
ecc(G) ≤ Lb(G) − k."

**Formalization Note** `n = |V|`; `t₁ ≥ t₂` the two largest part sizes of `G△M` (`0` beyond the
number of non-empty parts); the first inequality is compared in `ℝ`. A universal vertex is adjacent
to every other vertex. -/
theorem lemma_8 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (M : Finset (Sym2 V))
    (hM : IsPairSet M) (huniv : (universalVertices G).card ≤ 1)
    (hcm : (flip G M).IsCompleteMultipartite)
    (h₁ : (partSize (flip G M) 2 : ℝ) ≤ 1.5 * ((Fintype.card V : ℝ) - partSize (flip G M) 1 -
        partSize (flip G M) 2) + k + 4 * M.card)
    (h₂ : 300 * k + 150 * M.card ≤ Fintype.card V) :
    InLb G k := by sorry

end LovaszECCKernel
