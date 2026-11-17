-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_2
-- name    : GraphNNSphere.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:55:58.792204+00:00
-- url     : https://prove2.me/theorems/9a8d40be-3284-4ed3-b8ea-a052f465554f
-- title:
--   Theorem 5.2, pp.54–55 — greedy search from a uniform random entry fails below the critical degree
-- statement:
--   Fix $k\ge1$ and let the data be uniform.
--
--   1. In the logarithmic regime $d=\lfloor c\log n\rfloor$, fix $0<\beta<\beta^*(c)$ and let $\Delta=\lceil n^\beta\rceil$. There is $\eta>0$ such that, with probability at least $1-n^{-\eta}$ over the data, a query set of surface measure at least $1-n^{-\eta}$ has the following property: for every query in it, greedy navigation from a uniform random entry succeeds with probability at most $n^{-\eta}$ on either $G_{\rho_\beta}$ or $N_\Delta$, conditional on the data, the probability taken over the entry label.
--   2. In the dense regime, fix $0<\gamma<\gamma_c$ and let $\Delta=\lceil e^{\gamma d}\rceil$. There is $\zeta>0$ such that, with probability at least $1-e^{-\zeta d}$ over the data, a query set of surface measure at least $1-e^{-\zeta d}$ has the same property with bound $e^{-\zeta d}$, on either $G_{r_\gamma}$ or $N_\Delta$.
--
--   Below the critical degree, a single random start is therefore exponentially unlikely to find a target; this is the starting point for the exact restart exponent of Section 5.2.
--
--   **Formalization Note** Given the data, the success probability from a uniform entry is the fraction $\#\{x_0:W_G(q;x_0)<\infty\}/n$ of successful entries. One data event and one query set serve both graphs.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - encoding: probability over a uniform entry label, conditional on the data → the fraction #{x₀ : W_G(q; x₀) < ∞}/n; reason: same quantity
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.2, pp.54–55 (PDF pp.56–57)

import Mathlib
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_gammaC
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

open Classical in
/-- Theorem 5.2, random-entry failure (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.2, pp.54–55). For uniform data below the
critical degree, with high probability a query set of surface measure close to one has the
property that greedy navigation from a uniform random entry succeeds with probability at most
`n^{-η}` (logarithmic regime, on `G_{ρ_β}` and `N_Δ`) or `e^{-ζd}` (dense regime, on `G_{r_γ}` and `N_Δ`),
conditional on the sample.

**Formalization Note** The probability over a uniform entry label, given the sample, is the
fraction `#{x₀ : W_G(q; x₀) < ∞}/n` of successful entries. One data event and one query set serve
both graphs. Constants come before `d(·)`. -/
theorem theorem_5_2 :
    (∀ k : ℕ, 1 ≤ k → ∀ c β : ℝ, 0 < c → 0 < β → β < betaStar c →
      ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
        ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
          1 - (n : ℝ) ^ (-η) ≤ (dataLaw n (logDim c n) E).toReal ∧
          ∀ X ∈ E, ∃ QS : Set (Sph (logDim c n)), MeasurableSet QS ∧
            1 - (n : ℝ) ^ (-η) ≤ (unif (logDim c n) QS).toReal ∧
            ∀ q ∈ QS, ∀ G : NavGraph n,
              (G = thresholdGraph X (rhoBeta n (logDim c n) β) ∨ G = nnGraph X ⌈(n : ℝ) ^ β⌉₊) →
              ((Finset.univ.filter (fun x₀ : Fin n => W G X q k x₀ < ⊤)).card : ℝ) / n ≤
                (n : ℝ) ^ (-η)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ → γ < gammaC →
      ∃ ζ : ℝ, 0 < ζ ∧ ∀ d : ℕ → ℕ, IsDenseRegime d → ∀ᶠ n : ℕ in atTop,
        ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
          1 - Real.exp (-(ζ * (d n : ℝ))) ≤ (dataLaw n (d n) E).toReal ∧
          ∀ X ∈ E, ∃ QS : Set (Sph (d n)), MeasurableSet QS ∧
            1 - Real.exp (-(ζ * (d n : ℝ))) ≤ (unif (d n) QS).toReal ∧
            ∀ q ∈ QS, ∀ G : NavGraph n,
              (G = thresholdGraph X (rGamma n (d n) γ) ∨
                G = nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊) →
              ((Finset.univ.filter (fun x₀ : Fin n => W G X q k x₀ < ⊤)).card : ℝ) / n ≤
                Real.exp (-(ζ * (d n : ℝ)))) := by sorry

end Supplement

end GraphNNSphere
