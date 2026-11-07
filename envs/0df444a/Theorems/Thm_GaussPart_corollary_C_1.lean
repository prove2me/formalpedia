-- Prove2me | Theorems.Thm_GaussPart_corollary_C_1
-- name    : GaussPart.corollary_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:11.8902+00:00
-- url     : https://prove2.me/theorems/69a5bfb5-f564-4fa5-883c-2e960dddf8a5
-- title:
--   Corollary C.1 — confidence amplification of the moment discrepancy finder
-- statement:
--   Under the hypotheses of Proposition 3.3, for every $\beta\in(0,1/2)$ there is an algorithm (Algorithm 5) that draws $d^k\,O(k^{O(k)})\,V/\Delta^2\cdot\log(2/\beta)$ samples, runs in time
--   $$d^{O(k)}\exp\Big(O(k^{O(k)})\frac{H^2}{\Delta^2}\log\frac H\Delta\Big)V^{O(1)}\log^{O(1)}\frac2\beta,$$
--   returns Reject, None or a unit direction, and with probability at least $1-\beta$:
--   1. for every returned direction $w$ some degree $\ell\in[k]$ has $|\mathbb E_Q[(w\cdot x)^\ell]-\mathbb E_{Z\sim N(0,1)}[Z^\ell]|\ge\Delta/4$;
--   2. if it returns None, $Q$ matches its first $k$ directional moments with $N(0,I_d)$ with slack $\Delta$;
--   3. if every Hermite moment tensor has Frobenius norm at most $H$, it does not return Reject.
--
--   This is the finder Algorithm 1 calls, with $\beta$ small enough for a union bound over all cells.
--
--   **Formalization Note** As in Proposition 3.3: one arithmetic-only program with one constant $C$, inputs $(k,\Delta,V,H,\beta)$, bounds on every sample stream; item 2 is Definition 2.2 on $W=\mathbb R^d$.
--
--   Differences from the source:
--   - reading: Algorithm 5 → one ArithmeticOnly program of the sampling real RAM meeting its guarantee, chosen before all parameters and Q; reason: as for Proposition 3.3: Algorithm 5 runs Algorithm 2, whose exact singular subspaces are not arithmetic
--   - encoding: O(·) constants → one natural constant C: samples ≤ d^k·C·k^{Ck}·V/Δ²·log(2/β), work ≤ d^{Ck}·exp(C k^{Ck}(H²/Δ²) log(H/Δ))·V^C·log(2/β)^C; reason: uniform constants
--   - reading: draws at most … samples, runs in time … → the sample and work bounds hold on every sample stream, and every run halts; reason: worst-case reading of the budgets, the stronger one; Algorithm 1's budgets are fixed
--   - encoding: returns a unit direction → returns a nonzero vector ŵ; the direction is ŵ/∥ŵ∥ (decodeFinder); reason: an arithmetic machine has no square root; the normalization is exact in the specification
--   - encoding: E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial of degree ≤ k → PolyMomentBound Q V k: lower Lebesgue integrals of p², polynomials MvPolynomial (Fin d) ℝ of total degree ≤ k; reason: a Bochner integral of a non-integrable p² would be 0 and make the assumption vacuous
--   - encoding: with probability at least p → a measurable set of sample streams of i.i.d.-product measure at least p on which every halted state has the property; reason: outer probability of a non-measurable event would be weaker
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Corollary C.1, p.73 (PDF p.75); Algorithm 5, p.74 (PDF p.76); proof pp.74–75

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_MatchesMoments
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects
import Definitions.Def_GaussPart_decodeFinder

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussPart

/-- **Corollary C.1** (Confidence amplification of the moment discrepancy finder).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Corollary C.1, p.73 (PDF p.75); Algorithm 5, p.74
(PDF p.76); proof pp.74–75.

"Under the hypotheses of Proposition 3.3, for every β ∈ (0, 1/2), Algorithm 5 draws
d^k O(k^{O(k)}) V/∆² log(2/β) samples and runs in time
d^{O(k)} exp(O(k^{O(k)}) (H²/∆²) log(H/∆)) V^{O(1)} log^{O(1)}(2/β). It returns Reject, None, or a unit
direction. With probability at least 1 − β, all of the following hold: 1. For every returned
direction, there is a degree in [k] for which the corresponding directional moment differs from its
Gaussian reference value by at least ∆/4. 2. If the routine returns None, the distribution matches
directional moments with the standard Gaussian to slack ∆. 3. If every population Hermite moment
tensor has Frobenius norm at most H, the routine does not return Reject."

**Formalization Note.**
* As in `GaussPart.proposition_3_3`: "Algorithm 5" is one `ArithmeticOnly` program of the
  `GaussMixHH` machine with one constant `C : ℕ`, chosen before all parameters; it reads
  `k, ∆, V, H, β` (`amplifiedInput`); its output is decoded by `decodeFinder` (a direction is a
  nonzero vector, normalized). Bounds hold on every sample stream.
* Item 1: `|E_Q[(w · x)^ℓ] − E_{Z∼N(0,1)}[Z^ℓ]| ≥ ∆/4` (`gaussianMoment`). Item 2: Definition 2.2 on
  `W = ℝ^d`, `MatchesMoments N(0, I_d) Q ⊤ k ∆`. Item 3 as in Proposition 3.3.
* "With probability at least 1 − β": a measurable set of streams of measure at least `1 − β`. -/
theorem corollary_C_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P) (C : ℕ),
      ∀ (k d : ℕ), 1 ≤ k → 1 ≤ d → ∀ (Δ V H β : ℝ), 0 < Δ → Δ < 1 / 2 → 1 ≤ V → 1 ≤ H →
        0 < β → β < 1 / 2 →
      ∀ (Q : Measure (Vec d)) [IsProbabilityMeasure Q], PolyMomentBound Q V k →
        (∀ xs : ℕ → Vec d, ∃ t : ℕ,
          (GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β)) (noCoins, xs)
              t).halted = true ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β)) (noCoins, xs)
              t).samplesUsed : ℝ) ≤
            (d : ℝ) ^ k * (C * (k : ℝ) ^ (C * k)) * V / Δ ^ 2 * Real.log (2 / β) ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β)) (noCoins, xs)
              t).work : ℝ) ≤
            (d : ℝ) ^ (C * k) * Real.exp (C * (k : ℝ) ^ (C * k) * (H ^ 2 / Δ ^ 2) * Real.log (H / Δ)) *
              V ^ C * Real.log (2 / β) ^ C ∧
          decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β))
            (noCoins, xs) t) ≠ none) ∧
        ∃ E : Set (ℕ → Vec d), MeasurableSet E ∧
          ENNReal.ofReal (1 - β) ≤ Measure.infinitePi (fun _ : ℕ => Q) E ∧
          ∀ xs ∈ E, ∀ t : ℕ,
            (GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β)) (noCoins, xs)
              t).halted = true →
            (∀ w : Vec d, decodeFinder d (GaussMixHH.run P d
                (GaussMixHH.initState d (amplifiedInput k Δ V H β)) (noCoins, xs) t) = some (.dir w) →
              ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k ∧ Δ / 4 ≤ |∫ x, ⟪w, x⟫ ^ ℓ ∂Q - gaussianMoment ℓ|) ∧
            (decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β))
                (noCoins, xs) t) = some .none →
              MatchesMoments (stdGaussian (Vec d)) Q ⊤ k Δ) ∧
            ((∀ i : ℕ, 1 ≤ i → i ≤ k → frobeniusNorm (hermiteMoment Q i) ≤ H) →
              decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (amplifiedInput k Δ V H β))
                (noCoins, xs) t) ≠ some .reject) := by sorry

end GaussPart
