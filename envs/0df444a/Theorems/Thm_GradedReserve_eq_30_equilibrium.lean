-- Prove2me | Theorems.Thm_GradedReserve_eq_30_equilibrium
-- name    : GradedReserve.eq_30_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:34.270529+00:00
-- url     : https://prove2.me/theorems/eb026fcd-e43e-4208-82d3-719cf93ef6b4
-- title:
--   (30) — the equilibrium $\beta^*$ of the optimal graded reserve
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real), $n\ge2$ and $p>p_{\min}$, and let $\pi^*(b)=\min\{(b/b_0)^p,1\}$. Then the pure strategy
--   $$\beta^*(v)=\begin{cases}\frac{p+m}{p+\ell}v, & 0\le v\le\bar v,\\ \frac m\ell v+\frac{p\bar v^{\,\ell}}{\ell(p+\ell)v^m}, & \bar v\le v\le1,\end{cases}\qquad(30)$$
--   is a symmetric Bayes–Nash equilibrium of $G_{\pi^*}$, with probability of sale $\pi^*(\beta^*(v))=s^*(v)=\min\{(v/\bar v)^p,1\}$ for $v\in[0,1]$. The two bids agree at $\bar v$, and $\beta^*$ is increasing on $[0,1]$.
--
--   This shows the canonical mechanism attains the bound of the certificate (29).
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: symmetric BNE β, mixed strategies allowed (p.13), with an exit action → a Markov kernel σ from values to actions in ℝ; negative actions are exit, bids lie in [0,1], no mass above 1; reason: Lean convention (no measurable space on Option ℝ); the same strategies
--   - reading: a Bayes–Nash equilibrium (every type best-responds) → almost every type (for the value law) best-responds; reason: the paper's proofs work up to null sets of types ("apart from a null set", p.14); a single type has probability zero
--   - encoding: sells to the highest bidder with probability π(b₍₁₎); ties broken uniformly at random → W(b) = π(b) Σ_j C(n−1,j) a^j c^{n−1−j}/(j+1) against n − 1 i.i.d. opponents; reason: the same winning probability
--   - encoding: the pure strategy β* → the deterministic kernel v ↦ δ_{β*(v)}, with measurability of β* part of the conclusion; reason: the same strategy
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (30), p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_betaStar
import Definitions.Def_GradedReserve_cZero
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_piStar
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_sStar
import Definitions.Def_GradedReserve_vbar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Display (30)** (the equilibrium of the canonical mechanism) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (30), p.19,
PDF 20): for `F(v) = v^k`, every `n ≥ 2` and every `p > p_min`, the pure strategy `β*` of (30) is
a symmetric BNE of `G_{π*}`, `π*(b) = min{(b/b₀)^p, 1}`, with probability of sale
`π*(β*(v)) = s*(v) = min{(v/v̄)^p, 1}`; the two bids agree at `v̄` and `β*` is increasing.

**Formalization Note.** The pure strategy is the deterministic kernel `v ↦ δ_{β*(v)}`; its
measurability is part of the conclusion. -/
theorem eq_30_equilibrium (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (p : ℝ)
    (hp : pMin k n < p) :
    (∃ hβ : Measurable (betaStar k n p),
      IsSymBNE (powerDensity k) n (piStar k n p) (Kernel.deterministic (betaStar k n p) hβ)) ∧
    (∀ v ∈ Icc (0:ℝ) 1, piStar k n p (betaStar k n p v) = sStar k n p v) ∧
    cZero k n p * vbar k n p = powM k n / powL k n * vbar k n p
      + p * vbar k n p ^ powL k n / (powL k n * (p + powL k n) * vbar k n p ^ powM k n) ∧
    StrictMonoOn (betaStar k n p) (Icc 0 1) := by sorry

end GradedReserve
