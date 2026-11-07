-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_5
-- name    : LovaszECCKernel.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:09.575734+00:00
-- url     : https://prove2.me/theorems/d01d4615-12df-4135-bc1e-c1109ebe4ce5
-- title:
--   Lemma 5 — replacement in an m.c.d.s. whose cliques meet the modulator: $\mathrm{ecc}(G)\le|\mathcal C|-k$
-- statement:
--   **Lemma 5.** Let $G$ be a finite simple graph, $k\ge0$, $S\subseteq V(G)$, and $M$ a set of pairs of distinct vertices of $S$ such that $G\triangle M$ is complete multipartite. Let $C_1,\dots,C_t$ be an m.c.d.s. of $G$ such that
--   1. $|C_i\cap S|\ge1$ for each $i\in\{2,\dots,t\}$;
--   2. $C_i\setminus S$ is a maximal clique of $G_i-S$ for each $i\in\{1,\dots,t\}$;
--   3. $\sum_{i=2}^t|C_i\setminus S|\ge7|S|+10k$.
--
--   If $\mathcal C$ is the Lovász Clique Cover given by $C_1,\dots,C_t$, then
--   $$\mathrm{ecc}(G)\ \le\ |\mathcal C|-k .$$
--
--   Differences from the source:
--   - reading: an m.c.d.s. has t₂ ∈ [t] (Definition 1) → t₂ ∈ {0, …, t}; reason: edgeless graphs have only singleton cliques (t₂ = 0); the paper uses such sequences (Lovász's construction, step 7 of Lemma 8's proof), and the printed [t] would leave them without an m.c.d.s.; the Lean statement covers the printed sequences too
--   - encoding: cliques C₁, …, C_t, 1-based → a list indexed from 0; reason: Lean convention; the same sequences
--   - encoding: k from the surrounding text → k ∈ ℕ, the conclusion compared in ℤ; reason: the lemma does not quantify k itself; §3 fixes k ≥ 0
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 5, p.35 (= PDF p.35)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_flip
import Definitions.Def_LovaszECCKernel_IsMCDS
import Definitions.Def_LovaszECCKernel_LCC

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 5** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 5, p.35 (= PDF p.35)): "Let G be a graph, let S ⊆ V(G) and let
M ⊆ (S choose 2) be such that G△M is complete r-partite. Let C1, C2, . . . , Ct be a m.c.d.s. in G
such that
• |Ci ∩ S| ≥ 1 for each i ∈ {2, . . . , t},
• Ci \ S is a maximal clique in Gi − S for each i ∈ {1, . . . , t},
• Σ_{i=2}^{t} |Ci \ S| ≥ 7 · |S| + 10k.
If C is the LCC given by C1, C2, . . . , Ct, then ecc(G) ≤ |C| − k."

**Formalization Note** The m.c.d.s. is a list indexed from `0` (`L.getD i ∅` is the paper's
`C_{i+1}`, `remaining L i` the vertex set of `G_{i+1}`), so the paper's ranges `{2, …, t}` and
`{1, …, t}` are `1 ≤ i < t` and `0 ≤ i < t`. `M ⊆ (S choose 2)`: pairs of distinct vertices, both
in `S`. `k ∈ ℕ`; the conclusion is compared in `ℤ`, `|C|` the number of cliques of the LCC. -/
theorem lemma_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (M : Finset (Sym2 V)) (k : ℕ)
    (hM : IsPairSet M) (hMS : ∀ e ∈ M, ∀ v ∈ e, v ∈ S)
    (hcm : (flip G M).IsCompleteMultipartite)
    (L : List (Finset V)) (hL : IsMCDS G L)
    (h₁ : ∀ i, 1 ≤ i → i < L.length → 1 ≤ (L.getD i ∅ ∩ S).card)
    (h₂ : ∀ i, i < L.length → IsMaxCliqueIn G (remaining L i \ S) (L.getD i ∅ \ S))
    (h₃ : 7 * S.card + 10 * k ≤ ∑ i ∈ Finset.Ico 1 L.length, (L.getD i ∅ \ S).card) :
    (ecc G : ℤ) ≤ (LCC G L).card - k := by sorry

end LovaszECCKernel
