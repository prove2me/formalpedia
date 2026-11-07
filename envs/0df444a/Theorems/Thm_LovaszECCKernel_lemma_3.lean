-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_3
-- name    : LovaszECCKernel.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:19.050203+00:00
-- url     : https://prove2.me/theorems/7b059049-5862-4634-b9c7-6eefe6dc0475
-- title:
--   Lemma 3 — a large complete bipartite part with universal rest has $\mathrm{ecc}(G)=t_1t_2$
-- statement:
--   **Lemma 3.** Let $G$ be a finite simple graph on $n$ vertices and $T_1,T_2$ disjoint independent sets of sizes $t_1\ge t_2$ such that every vertex of $T_1$ is adjacent to every vertex of $T_2$ (so $G[T_1\cup T_2]$ is complete bipartite), and every vertex of $T_1\cup T_2$ is adjacent to every vertex outside $T_1\cup T_2$. Let $\alpha=\tfrac12(\sqrt3-1)$. If
--   $$t_2\ \ge\ (1+\alpha)(n-t_1-t_2),$$
--   then $\mathrm{ecc}(G)=t_1\cdot t_2$.
--
--   The lemma computes $\mathrm{ecc}$ exactly for graphs dominated by two parts; it is the base case of Lemma 4.
--
--   Differences from the source:
--   - encoding: α = ½·(√3 − 1) < 0.367 → α = (√3 − 1)/2 written out; the remark α < 0.367 is not stated; reason: the remark is a numerical fact about α, not a hypothesis or a conclusion
--   - encoding: the hypothesis t₂ ≥ (1 + α)(n − t₁ − t₂) → compared in ℝ with n = |V|; reason: real number α
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 3, p.32 (= PDF p.32)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 3** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 3, p.32 (= PDF p.32)): "Let G be an n-vertex graph where T1 and T2 are
disjoint independent sets of sizes t1 ≥ t2 respectively, such that G[T1 ∪ T2] is a complete
bipartite graph. Additionally, every v ∈ (T1 ∪ T2) is adjacent to every u ∈ V(G) \ (T1 ∪ T2). If
t2 ≥ (1 + α)(n − t1 − t2), then ecc(G) = t1 · t2, where α = 1/2 · (√3 − 1) < 0.367."

**Formalization Note** `n = |V|`; the hypothesis is compared in `ℝ` with `α = (√3 − 1)/2` written
out. "G[T1 ∪ T2] is complete bipartite" with independent `T₁, T₂` is: every vertex of `T₁` is
adjacent to every vertex of `T₂`. The remark `α < 0.367` is a fact about the number `α`, not a
hypothesis. -/
theorem lemma_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T₁ T₂ : Finset V)
    (hdisj : Disjoint T₁ T₂)
    (hind₁ : ∀ u ∈ T₁, ∀ v ∈ T₁, ¬ G.Adj u v) (hind₂ : ∀ u ∈ T₂, ∀ v ∈ T₂, ¬ G.Adj u v)
    (hle : T₂.card ≤ T₁.card)
    (hbip : ∀ u ∈ T₁, ∀ v ∈ T₂, G.Adj u v)
    (huniv : ∀ v ∈ T₁ ∪ T₂, ∀ u, u ∉ T₁ ∪ T₂ → G.Adj v u)
    (h : (1 + (Real.sqrt 3 - 1) / 2) * ((Fintype.card V : ℝ) - T₁.card - T₂.card) ≤ T₂.card) :
    ecc G = T₁.card * T₂.card := by sorry

end LovaszECCKernel
