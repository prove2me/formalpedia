-- Prove2me | Theorems.Thm_GnpColoring_theorem_4_1
-- name    : GnpColoring.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:18.708611+00:00
-- url     : https://prove2.me/theorems/b7c23265-5571-498e-b5ed-070852629e19
-- title:
--   Theorem 4.1 — $G(n,d/n)$ has a valid block partition
-- statement:
--   Given $A\ge0$, $C>0$ and $0<\eta<1/2$, there are $K>0$ and $d_0>1$ such that for all $d\ge d_0$, with $h=\lceil K\log n/d^{2\eta}\rceil$, with probability $1-o(1)$ as $n\to\infty$ over $G\sim G(n,d/n)$ there is a set $S\subseteq\hat S$ whose block partition is valid (Definition 3.2, with diameter constant $D=16(K+1)$) and every block $B$ satisfies
--
--   $$\operatorname{diam}(G[B])<16h\le16(K+1)\frac{\log n}{d^{2\eta}}.$$
--
--   This supplies the partition on which the block dynamics runs.
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - reading: "valid as specified by Definition 3.2" (diameter constant unspecified) → valid with $D=16(K+1)$; reason: the proof's choice (p.43); validity for any $D$ plus the stated diameter bound gives validity with $16(K+1)$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 4.1, pp.35–36

import Mathlib
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_blockDiam
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Theorem 4.1 (valid block partition in `G(n, d/n)`).** For fixed `A ≥ 0`, `C > 0` and `0 < η < 1/2`
there are `K > 0` and `d₀ > 1` such that for all `d ≥ d₀`, with `h = ⌈K log n / d^(2η)⌉`, with
probability `1 − o(1)` over `G ∼ G(n, d/n)` there is a set `S ⊆ Ŝ` whose block partition is valid
(Definition 3.2) and every block satisfies `diam(G[B]) < 16h ≤ 16(K + 1) log n / d^(2η)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 4.1, pp.35–36.

**Formalization Note** The diameter constant of Definition 3.2 is `D = 16(K + 1)`, the proof's
choice (p.43: "Set D = 16(K + 1)"); validity with this `D` is implied by validity with any `D`
together with the stated diameter bound, so nothing is lost. `S ⊆ Ŝ` is part of
`IsValidPartition`. `h` is the ceiling `⌈·⌉₊`. -/
theorem theorem_4_1 :
    ∀ A : ℝ, 0 ≤ A → ∀ C : ℝ, 0 < C → ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℝ, 1 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          ∃ S : Finset (Fin n), IsValidPartition G d η A C (16 * (K + 1)) S ∧
            (∀ B ∈ blocks G S, blockDiam G B < 16 * ⌈K * Real.log n / d ^ (2 * η)⌉₊) ∧
            ((16 * ⌈K * Real.log n / d ^ (2 * η)⌉₊ : ℕ) : ℝ) ≤
              16 * (K + 1) * Real.log n / d ^ (2 * η)))
        atTop (𝓝 1) := by sorry

end GnpColoring
