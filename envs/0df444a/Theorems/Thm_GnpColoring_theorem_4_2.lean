-- Prove2me | Theorems.Thm_GnpColoring_theorem_4_2
-- name    : GnpColoring.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:21.060019+00:00
-- url     : https://prove2.me/theorems/439674d2-bdde-475f-9d6d-dae95064099f
-- title:
--   Theorem 4.2 — small components after deleting breakpoints
-- statement:
--   Given $A\ge0$, $C>0$ and $0<\eta<1/2$, there are $K>0$ and $d_0>1$ such that for all $d\ge d_0$, with $h=\lceil K\log n/d^{2\eta}\rceil$, the following hold simultaneously with probability $1-o(1)$ as $n\to\infty$ over $G\sim G(n,d/n)$:
--
--   1. $G[V\setminus\hat S]$ contains no self-avoiding path on $8h$ vertices, and every $B\in\hat{\mathcal B}$ satisfies $\operatorname{diam}(G[B])<8h\le8(K+1)\log n/d^{2\eta}$;
--   2. every $G[B]$, $B\in\hat{\mathcal B}$, is a tree or unicyclic;
--   3. $\hat S_r=\hat S$ for every integer $r\ge h$.
--
--   Here $\hat{\mathcal B}$ are the components of $G$ after deleting the global breakpoints.
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - encoding: "no self-avoiding path on $8h$ vertices" → every self-avoiding path avoiding $\hat S$ has fewer than $8h$ vertices; reason: equivalent for $h\ge1$ (subpaths); $h=0$ only when $n\le1$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 4.2, p.36

import Mathlib
import Definitions.Def_GnpColoring_globalBreakpoints
import Definitions.Def_GnpColoring_rBreakpoints
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_blockDiam
import Definitions.Def_GnpColoring_IsTreeOrUnicyclic
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Theorem 4.2 (small components after deleting breakpoints).** For fixed `A ≥ 0`, `C > 0` and
`0 < η < 1/2` there are `K > 0` and `d₀ > 1` such that for all `d ≥ d₀`, with `h = ⌈K log n / d^(2η)⌉`,
with probability `1 − o(1)` over `G ∼ G(n, d/n)` simultaneously:
(i) `G[V ∖ Ŝ]` contains no self-avoiding path on `8h` vertices, and every `B ∈ 𝓑̂` has
`diam(G[B]) < 8h ≤ 8(K + 1) log n / d^(2η)`;
(ii) every `G[B]`, `B ∈ 𝓑̂`, is a tree or unicyclic;
(iii) `Ŝ_r = Ŝ` for every integer `r ≥ h`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 4.2, p.36.

**Formalization Note** `h` is the ceiling `⌈·⌉₊`. "No self-avoiding path on `8h` vertices" is
written as "every self-avoiding path of `G` avoiding `Ŝ` has fewer than `8h` vertices" (equivalent
for `h ≥ 1`, since a longer path contains one on exactly `8h` vertices; `h = 0` only for `n ≤ 1`).
`𝓑̂` is `blocks G Ŝ`; diameters are measured inside the blocks. -/
theorem theorem_4_2 :
    ∀ A : ℝ, 0 ≤ A → ∀ C : ℝ, 0 < C → ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℝ, 1 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          (∀ (u v : Fin n) (p : G.Walk u v), p.IsPath →
              (∀ w ∈ p.support, w ∉ globalBreakpoints G d η A C) →
              p.support.length < 8 * ⌈K * Real.log n / d ^ (2 * η)⌉₊) ∧
          (∀ B ∈ blocks G (globalBreakpoints G d η A C),
              blockDiam G B < 8 * ⌈K * Real.log n / d ^ (2 * η)⌉₊) ∧
          ((8 * ⌈K * Real.log n / d ^ (2 * η)⌉₊ : ℕ) : ℝ) ≤ 8 * (K + 1) * Real.log n / d ^ (2 * η) ∧
          (∀ B ∈ blocks G (globalBreakpoints G d η A C), IsTreeOrUnicyclic G B) ∧
          (∀ r : ℕ, ⌈K * Real.log n / d ^ (2 * η)⌉₊ ≤ r →
              rBreakpoints G d η A C r = globalBreakpoints G d η A C)))
        atTop (𝓝 1) := by sorry

end GnpColoring
