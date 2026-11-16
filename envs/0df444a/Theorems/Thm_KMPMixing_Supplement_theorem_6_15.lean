-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_6_15
-- name    : KMPMixing.Supplement.theorem_6_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:57:00.068206+00:00
-- url     : https://prove2.me/theorems/bd135ae7-39c1-4b27-8947-50020ddbe81b
-- title:
--   Theorem 6.15 — parallel KMP and partition resampling chains: $\mathrm{TV}\le d^2e^{-ck}$
-- statement:
--   For some absolute constant $c>0$, all even $d\ge2$ and all integers $t,k\ge1$:
--
--   1. for the parallel KMP chain $M_{\mathrm{PKMP}}$ on $\Delta=\{R\in\mathbb N^d:\sum_jR_j=t\}$ with its uniform stationary law $\pi_{\mathrm{PKMP}}$,
--   $$
--   \sup_{r\in\Delta}\|M^k_{\mathrm{PKMP}}(r,\cdot)-\pi_{\mathrm{PKMP}}\|_{\mathrm{TV}}\le d^2e^{-ck};
--   $$
--   2. for the partition resampling chain $M$ on $Y_{t,d}$ with stationary law $\pi(\lambda)=|\Xi_{\lambda,d}|/\binom{t+d-1}{d-1}$,
--   $$
--   \sup_{\lambda\in Y_{t,d}}\|M^k(\lambda,\cdot)-\pi\|_{\mathrm{TV}}\le d^2e^{-ck}.
--   $$
--
--   Both bounds are independent of the number of particles $t$; the second drives the convergence of the parallel Kac twirl (Theorem 6.1).
--
--   **Formalization Note** $c$ is quantified before $d,t,k$. Total variation is `MarkovMixing.tvDist` of the $k$-step row; the suprema over the finite state spaces are written as "for every". $Y_{t,d}$ is encoded as non-increasing vectors of $\Delta$.
--
--   Differences from the source:
--   - encoding: partitions λ ∈ Y_{t,d} and the type r↓ → zero-padded non-increasing vectors of State d t, and 'some rearrangement of r equals the padded λ'; reason: a bijection with Y_{t,d}; Definition 6.9 itself pads λ with zeros
--   - encoding: a uniformly random perfect matching of [d] → the uniform average over fixed-point-free involutions of Fin d; reason: perfect matchings of the complete graph are in bijection with fixed-point-free involutions
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem 6.15, p.50 (PDF p.52), restated p.76 (PDF p.78); Definitions 6.9 and 6.13, Lemmas 6.11 and 6.14

import Mathlib
import Definitions.Def_KMPMixing_Supplement_parallelKMP

namespace KMPMixing.Supplement

open MarkovMixing KMPMixing

/-- **Theorem 6.15** (arXiv:2609.38044, p.50 (PDF p.52); restated p.76 (PDF p.78)). For some
absolute constant `c > 0`, all even `d ≥ 2` and all integers `t, k ≥ 1`,
`sup_{r ∈ Δ} ‖M^k_PKMP(r, ·) − π_PKMP‖_TV ≤ d² · e^{−ck}` and
`sup_{λ ∈ Y_{t,d}} ‖M^k(λ, ·) − π‖_TV ≤ d² · e^{−ck}`, where `M_PKMP` is the parallel KMP chain
on `Δ` with uniform stationary law `π_PKMP` (Lemma 6.14) and `M` is the partition resampling
chain on `Y_{t,d}` with stationary law `π(λ) = |Ξ_{λ,d}| / C(t + d − 1, d − 1)` (Lemma 6.11).

**Formalization Note** `c` is quantified before `d`, `t`, `k`. `‖·‖_TV` is
`MarkovMixing.tvDist` of the row `M^k(x, ·)` (`rowDist`); the suprema over the finite state
spaces are written as `∀`. `π_PKMP` is `uniformDist (State d t)`. `Y_{t,d}` is encoded as the
non-increasing vectors of `State d t` (`PartitionState d t`). -/
theorem theorem_6_15 :
    ∃ c : ℝ, 0 < c ∧
      ∀ d : ℕ, Even d → 2 ≤ d →
      ∀ t k : ℕ, 1 ≤ t → 1 ≤ k →
        (∀ r : State d t,
          tvDist (rowDist (pkmpChain d t) k r) (uniformDist (State d t)) ≤
            (d : ℝ) ^ 2 * Real.exp (-c * k)) ∧
        (∀ lam : PartitionState d t,
          tvDist (rowDist (partitionChain d t) k lam) (partitionStationary d t) ≤
            (d : ℝ) ^ 2 * Real.exp (-c * k)) := by sorry

end KMPMixing.Supplement
