-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_7
-- name    : LovaszECCKernel.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:13.225312+00:00
-- url     : https://prove2.me/theorems/4dc4df18-270b-4d3a-848e-91bec82a6d87
-- title:
--   Lemma 7 — complete multipartite graphs with $t_3-t_8\ge\max\{4\sqrt k,7\}$: $\mathrm{ecc}(G)\le|\mathcal C|-k$
-- statement:
--   **Lemma 7.** Let $G$ be a complete multipartite graph with part sizes $t_1\ge t_2\ge\cdots$ (zero beyond the number of non-empty parts), and $k\ge0$, such that
--   $$t_3-t_8\ \ge\ \max\{4\sqrt k,\,7\}.$$
--   Then for the Lovász Clique Cover $\mathcal C$ of every m.c.d.s. of $G$,
--   $$\mathrm{ecc}(G)\ \le\ |\mathcal C|-k .$$
--
--   Differences from the source:
--   - reading: an m.c.d.s. has t₂ ∈ [t] (Definition 1) → t₂ ∈ {0, …, t}; reason: edgeless graphs have only singleton cliques (t₂ = 0); the paper uses such sequences (Lovász's construction, step 7 of Lemma 8's proof), and the printed [t] would leave them without an m.c.d.s.; the Lean statement covers the printed sequences too
--   - encoding: t₃, t₈ → the third and eighth largest part sizes, 0 beyond the number of non-empty parts; reason: empty parts have size 0
--   - encoding: k from the surrounding text → k ∈ ℕ, the hypothesis in ℝ and the conclusion in ℤ; reason: the lemma does not quantify k itself; §3 fixes k ≥ 0
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 7, p.37 (= PDF p.37)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_partSize
import Definitions.Def_LovaszECCKernel_IsMCDS
import Definitions.Def_LovaszECCKernel_LCC

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 7** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 7, p.37 (= PDF p.37)): "Let G be a complete r-partite graph such that
t3 − t8 ≥ max{4√k, 7}. Let C be an LCC of G. Then ecc(G) ≤ |C| − k."

**Formalization Note** `t₃, t₈` are the third and eighth largest part sizes (`0` beyond the number of
non-empty parts); the hypothesis is compared in `ℝ`. "An LCC": the LCC of every m.c.d.s. of `G`.
`k ∈ ℕ`. -/
theorem lemma_7 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hcm : G.IsCompleteMultipartite)
    (h : max (4 * Real.sqrt k) 7 ≤ (partSize G 3 : ℝ) - partSize G 8)
    (L : List (Finset V)) (hL : IsMCDS G L) :
    (ecc G : ℤ) ≤ (LCC G L).card - k := by sorry

end LovaszECCKernel
