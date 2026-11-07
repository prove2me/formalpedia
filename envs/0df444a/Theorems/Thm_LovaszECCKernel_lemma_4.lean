-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_4
-- name    : LovaszECCKernel.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:43.7196+00:00
-- url     : https://prove2.me/theorems/dbc2a24f-f687-4e20-87ab-fc1c8a3d0d61
-- title:
--   Lemma 4 — two dominant parts: $\mathrm{ecc}(G)=|E_G(T_1,T_2)|$ or $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$
-- statement:
--   **Lemma 4.** Let $G$ be a finite simple graph on $n$ vertices, $k\ge0$, and $M\subseteq\binom{V(G)}{2}$ such that $G\triangle M$ is complete multipartite with part sizes $t_1\ge t_2\ge\cdots$ satisfying
--   $$t_2\ \ge\ (1+\alpha)(n-t_1-t_2)+4|M|+k,\qquad\alpha=\tfrac12(\sqrt3-1).$$
--   Let $T_1,T_2$ be two largest parts of $G\triangle M$. Then
--   1. if no pair of $M$ has both ends in $T_1$ and none has both ends in $T_2$, then $\mathrm{ecc}(G)=|E_G(T_1,T_2)|$;
--   2. otherwise $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$.
--
--   In the kernel (Algorithm 1, lines 16–21) this case is decided exactly, without output of a reduced graph.
--
--   Differences from the source:
--   - encoding: ecc(G) = E_G(T1, T2) → ecc G = |E_G(T₁, T₂)|, the number of edges between T₁ and T₂; reason: the printed bullet omits |·|; the proof computes the number (C = |E_{G1}(T1, T2)|, p.33)
--   - reading: T₁, T₂ the two largest parts of G△M → every choice of two disjoint parts of sizes t₁, t₂ (T₂ = ∅ if there is one part); reason: ties are not resolved by the paper and its proof works for every choice; the Lean statement covers each choice
--   - encoding: part sizes t₁ ≥ t₂ of a complete r-partite graph whose parts may be empty → sizes of the non-empty parts in non-increasing order, padded with 0; reason: empty parts have size 0
--   - encoding: k from the surrounding text (an integer k ≥ 0) → k ∈ ℕ, the hypothesis compared in ℝ; reason: the lemma does not quantify k itself; §3 fixes k ≥ 0
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 4, pp.32–33 (= PDF pp.32–33)

import Mathlib
import Definitions.Def_LovaszECCKernel_InLb
import Definitions.Def_LovaszECCKernel_flip
import Definitions.Def_LovaszECCKernel_partSize
import Definitions.Def_LovaszECCKernel_crossEdges

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 4** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 4, pp.32–33 (= PDF pp.32–33)): "Let G be a graph and let M be a subset of
(V(G) choose 2), such that G△M is a complete r-partite graph with
t2 ≥ (1 + α) · (n − t1 − t2) + 4|M| + k.
Then
• ecc(G) = E_G(T1, T2), if M ∩ (Ti choose 2) = ∅ for each i ∈ {1, 2};
• ecc(G) ≤ Lb(G) − k, otherwise."

**Formalization Note** `n = |V|`, `α = (√3 − 1)/2` (Lemma 3), `t₁ ≥ t₂` the two largest part sizes
of `G△M` (zero if there are fewer parts), and `T₁, T₂` **any** two largest parts of `G△M`
(`IsTwoLargestParts`; `T₂ = ∅` if `G△M` has one part). The first bullet's `E_G(T1, T2)` is the
number of edges between `T₁` and `T₂` (`crossEdges`), as in the proof ("C = |E_{G1}(T1, T2)|").
`M ∩ (Ti choose 2) = ∅` says that no pair of `M` has both ends in `Tᵢ`. `k ∈ ℕ`; the hypothesis is
compared in `ℝ`. -/
theorem lemma_4 {V : Type*} [Fintype V] (G : SimpleGraph V) (M : Finset (Sym2 V)) (k : ℕ)
    (hM : IsPairSet M) (hcm : (flip G M).IsCompleteMultipartite)
    (h : (1 + (Real.sqrt 3 - 1) / 2) * ((Fintype.card V : ℝ) - partSize (flip G M) 1 -
        partSize (flip G M) 2) + 4 * M.card + k ≤ partSize (flip G M) 2)
    (T₁ T₂ : Finset V) (hT : IsTwoLargestParts (flip G M) T₁ T₂) :
    ((∀ e ∈ M, ¬ (∀ v ∈ e, v ∈ T₁) ∧ ¬ (∀ v ∈ e, v ∈ T₂)) → ecc G = crossEdges G T₁ T₂) ∧
    ((∃ e ∈ M, (∀ v ∈ e, v ∈ T₁) ∨ (∀ v ∈ e, v ∈ T₂)) → InLb G k) := by sorry

end LovaszECCKernel
