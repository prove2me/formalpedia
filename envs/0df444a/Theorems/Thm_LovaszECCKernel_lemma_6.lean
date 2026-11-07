-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_6
-- name    : LovaszECCKernel.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:16.267225+00:00
-- url     : https://prove2.me/theorems/1aeeab6d-8e9e-4c3d-aece-82c5b63b5152
-- title:
--   Lemma 6 — complete multipartite graphs with $\sum_i(\min\{t_i,t_8\}-1)\ge10k$: $\mathrm{ecc}(G)\le|\mathcal C|-k$
-- statement:
--   **Lemma 6.** Let $G$ be a complete multipartite graph with part sizes $t_1\ge t_2\ge\cdots\ge t_r$ ($r$ the number of non-empty parts, $t_8=0$ if $r<8$), and $k\ge0$, such that
--   $$\sum_{i=1}^r\bigl(\min\{t_i,t_8\}-1\bigr)\ \ge\ 10k .$$
--   Then for the Lovász Clique Cover $\mathcal C$ of every m.c.d.s. of $G$,
--   $$\mathrm{ecc}(G)\ \le\ |\mathcal C|-k .$$
--
--   Differences from the source:
--   - reading: an m.c.d.s. has t₂ ∈ [t] (Definition 1) → t₂ ∈ {0, …, t}; reason: edgeless graphs have only singleton cliques (t₂ = 0); the paper uses such sequences (Lovász's construction, step 7 of Lemma 8's proof), and the printed [t] would leave them without an m.c.d.s.; the Lean statement covers the printed sequences too
--   - reading: Σ_{i=1}^{r} over the parts of a complete r-partite graph (parts may be empty) → the sum over the non-empty parts; reason: an empty part would add −1, so this is the weakest form of the hypothesis; the proof uses |C₁| = r, the number of non-empty parts
--   - encoding: t₈ → the eighth largest part size, 0 if there are fewer than eight non-empty parts; reason: empty parts have size 0
--   - encoding: k from the surrounding text → k ∈ ℕ, the comparisons in ℤ; reason: the lemma does not quantify k itself; §3 fixes k ≥ 0
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 6, p.36 (= PDF p.36)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_partSize
import Definitions.Def_LovaszECCKernel_IsMCDS
import Definitions.Def_LovaszECCKernel_LCC

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 6** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 6, p.36 (= PDF p.36)): "Let G be a complete r-partite graph such that
Σ_{i=1}^{r} (min{ti, t8} − 1) ≥ 10k. Let C be an LCC of G. Then ecc(G) ≤ |C| − k."

**Formalization Note** The sum runs over the non-empty parts `P` of `G` (`t_i = |P|`), computed in
`ℤ`; `t₈` is the eighth largest part size, `0` if `G` has fewer than eight non-empty parts. "An
LCC": the LCC of every m.c.d.s. `L` of `G`. `k ∈ ℕ`. -/
theorem lemma_6 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hcm : G.IsCompleteMultipartite)
    (h : (10 * k : ℤ) ≤ ∑ P ∈ parts G, ((min P.card (partSize G 8) : ℤ) - 1))
    (L : List (Finset V)) (hL : IsMCDS G L) :
    (ecc G : ℤ) ≤ (LCC G L).card - k := by sorry

end LovaszECCKernel
