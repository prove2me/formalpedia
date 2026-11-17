-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_4_4
-- name    : GraphNNSphere.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:53:18.318529+00:00
-- url     : https://prove2.me/theorems/4ef98272-af4b-4a34-82c9-aa22af6b2a72
-- title:
--   Theorem 4.4, p.42 — nearest-neighbor navigation in the logarithmic regime
-- statement:
--   Fix $c>0$, $\beta^*(c)<\beta<1$, $k\ge1$ and $\bar\mu,\kappa\ge0$; let $d=\lfloor c\log n\rfloor$, $\Delta=\lceil n^\beta\rceil$, $\lambda=1/c$ and $\gamma=\beta/c$. Suppose that $\kappa<h(\gamma,\lambda+\bar\mu)$, with the two-argument $h$ of p.42. Let the sampling density satisfy
--
--   $$Me^{-\kappa d-2\vartheta_d}\le f\le M\quad\text{almost everywhere, for some }M\le e^{\bar\mu d+\vartheta_d}.$$
--
--   Then for every absolutely continuous query law $Q$ fixed before sampling, with probability $1-e^{-\Omega(d)}$ over the data, $N_\Delta$ succeeds from every entry for every query outside a set of $Q$-probability $e^{-\Omega(d)}$; each run uses $O(1)$ complete expansions and has evaluation cost $O(\Delta)$. The constants depend only on $(c,\beta,\bar\mu,\kappa)$, and the threshold for large $n$ may also depend on the fixed sequence $\vartheta_d=o(d)$.
--
--   In the logarithmic regime the density level shifts the local nearest-neighbor angle, so the sufficient condition for $N_\Delta$ involves both the largest density level $e^{\bar\mu d}$ and the global density ratio $e^{\kappa d}$.
--
--   **Formalization Note** The constants come before $k$ and $\vartheta$; the threshold depends on $k$ and $\vartheta$ only, and the density, $M$ and $Q$ are chosen after it (so they may vary with $n$).
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - encoding: fixed sequence ϑ_d = o(d) (with ϑ_d ≥ log 4, p.42) → an admissible slack sequence indexed by d, evaluated at d = ⌊c log n⌋; reason: same sequence
--   - encoding: O(1) complete expansions, evaluation cost O(Δ) → expansions ≤ H, evaluations ≤ CΔ for constants H, C; reason: explicit constants
--   - reading: "the threshold for sufficiently large n may also depend on the fixed sequence ϑ_d" → one threshold, chosen after (c, β, µ̄, κ, k, ϑ) and before the density f, the level M and the query law Q, so f, M and Q may vary with n; reason: the sentence names what the constants and the threshold depend on; this is the stronger reading, and a fixed density sequence and fixed Q are instances
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.4, p.42 (PDF p.44); R, X, h(g, ν) and ϑ_d, p.42

import Mathlib
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw
import Definitions.Def_GraphNNSphere_Supplement_hLog
import Definitions.Def_GraphNNSphere_Supplement_DClass

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

/-- Theorem 4.4, nearest-neighbor navigation in the logarithmic regime (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.4, p.42).
Let `d = ⌊c log n⌋`, `β*(c) < β < 1`, `Δ = ⌈n^β⌉`, `λ = 1/c`, `γ = β/c`, `μ̄, κ ≥ 0` with
`κ < h(γ, λ + μ̄)`. If `M e^{-κd - 2ϑ_d} ≤ f ≤ M` a.e. for some `M ≤ e^{μ̄ d + ϑ_d}`, then for every
absolutely continuous query law `Q`, with probability `1 - e^{-Ω(d)}` `N_Δ` succeeds from every entry for
every query outside a set of `Q`-probability `e^{-Ω(d)}`, each run using `O(1)` complete expansions and
evaluation cost `O(Δ)`. The constants depend only on `(c, β, μ̄, κ)`; the threshold for large `n`
may also depend on `ϑ_d = o(d)`.

**Formalization Note** The constants come before `k` and `ϑ`, the threshold comes after `k` and `ϑ`
and before the density, `M` and `Q`, which may all depend on `n`. `h` is the two-argument `hLog`
of p.42. `ϑ` is an admissible slack sequence (`ϑ_d = o(d)`, `ϑ_d ≥ log 4`), indexed by `d`. -/
theorem theorem_4_4 :
    ∀ c β : ℝ, 0 < c → betaStar c < β → β < 1 → ∀ μbar κ : ℝ, 0 ≤ μbar → 0 ≤ κ →
      κ < hLog (β / c) (1 / c + μbar) →
      ∃ c₁ c₂ H C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < H ∧ 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ϑ : ℕ → ℝ, IsSlackSeq ϑ →
      ∀ᶠ n : ℕ in atTop,
        ∀ f : Sph (logDim c n) → ℝ, IsDensity (logDim c n) f →
        (∃ M : ℝ, M ≤ Real.exp (μbar * (logDim c n : ℝ) + ϑ (logDim c n)) ∧
          ∀ᵐ x ∂(unif (logDim c n)),
            M * Real.exp (-(κ * (logDim c n : ℝ)) - 2 * ϑ (logDim c n)) ≤ f x ∧ f x ≤ M) →
        ∀ Q : Measure (Sph (logDim c n)), IsProbabilityMeasure Q → Q ≪ unif (logDim c n) →
        ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
          1 - Real.exp (-(c₁ * (logDim c n : ℝ))) ≤ (dataLawF n (logDim c n) f E).toReal ∧
          ∀ X ∈ E, ∃ B : Set (Sph (logDim c n)), MeasurableSet B ∧
            (Q B).toReal ≤ Real.exp (-(c₂ * (logDim c n : ℝ))) ∧
            ∀ q ∉ B, ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
              greedyRun (nnGraph X ⌈(n : ℝ) ^ β⌉₊) X q k x₀ = .success moves expansions evals ∧
              (expansions : ℝ) ≤ H ∧ (evals : ℝ) ≤ C * (⌈(n : ℝ) ^ β⌉₊ : ℝ) := by sorry

end Supplement

end GraphNNSphere
