-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_theorem_1_3
-- name    : NonMarkovColorings.Main.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:47.443652+00:00
-- url     : https://prove2.me/theorems/d510c4d8-e470-4f6d-93bf-8459a5a32e64
-- title:
--   Theorem 1.3 — Metropolis Glauber dynamics on $k$-colorings mixes in $O(n\log n)$ steps for $k\ge(1+\delta)\Delta$, girth $\ge7$, $\Delta\ge\Delta_0(\delta)$
-- statement:
--   A **$k$-coloring** of a finite graph $G=(V,E)$ is a map $\chi:V\to[k]$ with $\chi(v)\ne\chi(w)$ for every edge; $\Omega$ is the set of $k$-colorings and $\pi$ the uniform distribution on $\Omega$. The **Metropolis Glauber dynamics** (Definition 1.1) picks a uniform vertex $u$ and a uniform color $c$ and recolors $u$ with $c$ if the result is proper; equivalently it moves to each proper coloring at Hamming distance $1$ with probability $1/(nk)$ and stays put otherwise. Its **mixing time** $T_{mix}$ is the least $t$ with $\max_{X_0\in\Omega}\|P^t(X_0,\cdot)-\pi\|_{TV}\le1/4$. Theorem 1.3: for every $\delta>0$ there exist constants $\Delta_0(\delta)$ and $C(\delta)>0$ such that for every graph $G$ of maximum degree $\Delta\ge\Delta_0$ and girth $\ge7$ and every $k\ge(1+\delta)\Delta$,
--   $$T_{mix}\le C(\delta)\,n\log n .$$
--   This is optimal mixing of the Glauber dynamics for $k$ arbitrarily close to $\Delta$ under only a girth-$7$ and large-degree assumption.
--
--   **Formalization Note.** The chain is the published `MarkovMixing.coloringMetropolis G k` on proper colorings and $\pi$ is `uniformDist`; $T_{mix}\le X$ is written as "some $t\le X$ has $d(t)\le1/4$" (`distStationary`), which is equivalent and avoids `tMix`'s value $0$ on an empty set.
--
--   Differences from the source:
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
--   - encoding: T_mix ≤ C n log n with T_mix = min{t : d(t) ≤ 1/4} → ∃ t : ℕ, t ≤ C n log n ∧ distStationary P π t ≤ 1/4; reason: min S ≤ X iff some element of S is ≤ X; MarkovMixing.tMix is sInf, which is 0 on an empty set
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 2, Theorem 1.3 (proof p. 69)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_mm_coupling

namespace NonMarkovColorings.Main

/-- Theorem 1.3. For every `δ > 0` there are constants `Δ0(δ)` and `C(δ) > 0` such that for
every finite graph `G` on `n` vertices of maximum degree `Δ ≥ Δ0` and girth `≥ 7` and every
`k ≥ (1 + δ)Δ`, the Metropolis Glauber dynamics on proper `k`-colorings has mixing time at most
`C n log n`: some `t ≤ C n log n` has `max_{X0} ‖P^t(X0, ·) − π‖_TV ≤ 1/4`, `π` uniform on the
proper `k`-colorings. -/
theorem theorem_1_3 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Δ0 : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∃ t : ℕ, (t : ℝ) ≤ C * (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) ∧
        MarkovMixing.distStationary (MarkovMixing.coloringMetropolis G k)
          (MarkovMixing.uniformDist {c : V → Fin k // MarkovMixing.IsProperColoring G c}) t ≤
          1 / 4 := by sorry

end NonMarkovColorings.Main
