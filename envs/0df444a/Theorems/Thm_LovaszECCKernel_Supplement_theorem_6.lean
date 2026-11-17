-- Prove2me | Theorems.Thm_LovaszECCKernel_Supplement_theorem_6
-- name    : LovaszECCKernel.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:13:11.970377+00:00
-- url     : https://prove2.me/theorems/5dea28fe-354c-4422-9040-890ceb3e2cea
-- title:
--   Theorem 6 (Stability for Erdős–Goodman–Pósa) — $\mathrm{ecp}(G)\ge\lfloor n^2/4\rfloor-k$ implies $115k$ edits to complete bipartite
-- statement:
--   **Theorem 6 (Stability for the Erdős–Goodman–Pósa theorem).** For every integer $k\ge0$ and every graph $G$ on $n$ vertices, if
--   $$\mathrm{ecp}(G)\ \ge\ \Big\lfloor\frac{n^2}{4}\Big\rfloor-k,$$
--   then there is a set $M\subseteq\binom{V(G)}{2}$ of at most $115k$ pairs of distinct vertices such that $G\triangle M$ is complete bipartite.
--
--   This is a fine-grained stability theorem: a graph whose clique partition number is within $k$ of the Erdős–Goodman–Pósa bound is $O(k)$ edge edits from the extremal structure, with a constant independent of $n$. For $k=0$ it says that $\mathrm{ecp}(G)=\lfloor n^2/4\rfloor$ forces $G$ to be complete bipartite. It drives the kernel of Theorem 4.
--
--   **Formalization Note** The hypothesis is compared in $\mathbb Z$ (if $\lfloor n^2/4\rfloor<k$ it holds trivially and the conclusion must still hold). $G\triangle M$ is the published `flip`, and a complete bipartite graph may have an empty side.
--
--   Differences from the source:
--   - encoding: the hypothesis ecp(G) ≥ ⌊n²/4⌋ − k → compared in ℤ, k ∈ ℕ; reason: ⌊n²/4⌋ − k may be negative
--   - encoding: M ⊆ (V(G) choose 2) → a finite set of unordered pairs with no diagonal pair (IsPairSet); reason: the same sets
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 6, p.6 (= PDF p.6); restated p.44, proof pp.44–50

import Mathlib
import Definitions.Def_LovaszECCKernel_Supplement_ecp
import Definitions.Def_LovaszECCKernel_Supplement_IsCompleteBipartite
import Definitions.Def_LovaszECCKernel_flip

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- **Theorem 6 (Stability for Erdős–Goodman–Pósa Theorem)** (Fomin, Golovach, Khargeliia, Sagunov,
Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa
Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 6, p.6 (= PDF p.6); restated
word for word on p.44, proof pp.44–50): "For any integer k ≥ 0 and any n-vertex graph G, if
ecp(G) ≥ ⌊n²/4⌋ − k, then there exists a set M ⊆ (V(G) choose 2) of size at most 115k such that
G△M is complete bipartite."

**Formalization Note** The hypothesis is compared in `ℤ` (`⌊n²/4⌋ − k` may be negative, and then the
hypothesis holds trivially). `M` is a finite set of unordered pairs of distinct vertices
(`IsPairSet`), `G△M` is the published `flip G M`, and complete bipartite allows an empty side. -/
theorem theorem_6 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h : ((Fintype.card V ^ 2 / 4 : ℕ) : ℤ) - k ≤ ecp G) :
    ∃ M : Finset (Sym2 V), IsPairSet M ∧ M.card ≤ 115 * k ∧
      IsCompleteBipartite (flip G M) := by sorry

end LovaszECCKernel.Supplement
