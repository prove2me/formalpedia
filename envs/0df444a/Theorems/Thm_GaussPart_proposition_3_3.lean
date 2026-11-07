-- Prove2me | Theorems.Thm_GaussPart_proposition_3_3
-- name    : GaussPart.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:14.577307+00:00
-- url     : https://prove2.me/theorems/43ce846d-24bb-4383-be63-fe559ff16a82
-- title:
--   Proposition 3.3 — moment discrepancy finder
-- statement:
--   Let $k,d\ge1$, $\Delta\in(0,1/2)$, $V,H\ge1$, $P=N(0,I_d)$, and let $Q$ be a distribution on $\mathbb R^d$ with $\mathbb E_Q[p^2]\le V\|p\|^2_{L^2(P)}$ for every polynomial $p$ of degree at most $k$. There is an algorithm (Algorithm 2) that draws $d^k\,O(k^{O(k)})\,V/\Delta^2$ samples from $Q$, runs in time
--   $$d^{O(k)}\exp\Big(O(k^{O(k)})\frac{H^2}{\Delta^2}\log\frac H\Delta\Big)V^{O(1)},$$
--   returns Reject, None, or a unit direction, and with probability at least $2/3$:
--   1. if it returns a direction $w$, then $|\mathbb E_Q[(w\cdot x)^\ell]-\mathbb E_P[(w\cdot x)^\ell]|\ge3\Delta/8$ for some $\ell\in[k]$;
--   2. if it returns None, then $|\mathbb E_Q[(v\cdot x)^\ell]-\mathbb E_P[(v\cdot x)^\ell]|<\Delta$ for every unit $v$ and every $\ell\in[k]$;
--   3. if every Hermite moment tensor $A_i=\mathbb E_Q[\mathcal H_i]$, $i\in[k]$, has $\|A_i\|_F\le H$, it does not return Reject.
--
--   Algorithm 1 calls this finder (amplified, Corollary C.1) on the $V_R^\perp$ projection of $Q\mid R$ for each active cell.
--
--   **Formalization Note** "Algorithm 2" is one arithmetic-only program of the sampling real RAM with one constant $C$; samples $\le d^kCk^{Ck}V/\Delta^2$ and work $\le d^{Ck}\exp(Ck^{Ck}(H^2/\Delta^2)\log(H/\Delta))V^C$ on every sample stream, and every run halts with a well-formed output.
--
--   Differences from the source:
--   - reading: Algorithm 2 → one ArithmeticOnly program of the sampling real RAM meeting Algorithm 2's guarantee, chosen before all parameters and Q; reason: Algorithm 2 computes exact singular subspaces, which arithmetic does not; the paper's cost unit is "arithmetic operations" (p.35)
--   - encoding: O(·) constants → one natural constant C: samples ≤ d^k·C·k^{Ck}·V/Δ², work ≤ d^{Ck}·exp(C k^{Ck}(H²/Δ²) log(H/Δ))·V^C; reason: uniform constants
--   - reading: draws at most … samples, runs in time … → the sample and work bounds hold on every sample stream, and every run halts; reason: worst-case reading of the budgets, the stronger one; Algorithm 1's budgets are fixed
--   - encoding: returns a unit direction → returns a nonzero vector ŵ; the direction is ŵ/∥ŵ∥ (decodeFinder); reason: an arithmetic machine has no square root; the normalization is exact in the specification
--   - encoding: E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial of degree ≤ k → PolyMomentBound Q V k: lower Lebesgue integrals of p², polynomials MvPolynomial (Fin d) ℝ of total degree ≤ k; reason: a Bochner integral of a non-integrable p² would be 0 and make the assumption vacuous
--   - encoding: with probability at least p → a measurable set of sample streams of i.i.d.-product measure at least p on which every halted state has the property; reason: outer probability of a non-measurable event would be weaker
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Proposition 3.3, p.15 (PDF p.17); Algorithm 2, p.29 (PDF p.31); proof pp.30–35

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects
import Definitions.Def_GaussPart_decodeFinder

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Proposition 3.3** (Moment Discrepancy Finder).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Proposition 3.3, p.15 (PDF p.17); Algorithm 2, p.29;
proof pp.30–35.

"Let k, d ∈ ℤ₊, ∆ ∈ (0, 1/2), and V, H ≥ 1. Let P = N(0, I_d) and let Q be a distribution over ℝ^d
satisfying E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial p of degree at most k. Algorithm 2
draws d^k O(k^{O(k)}) (V/∆²) samples from Q, runs in d^{O(k)} exp(O(k^{O(k)}) (H²/∆²) log(H/∆)) V^{O(1)}
time and returns Reject, None, or a unit direction. With probability at least 2/3, all of the
following hold: 1. If the algorithm returns a direction w, then for some ℓ ∈ [k],
|E_{x∼Q}[(w · x)^ℓ] − E_{x∼P}[(w · x)^ℓ]| ≥ 3∆/8. 2. If the algorithm returns None, then for every
unit vector v and every ℓ ∈ [k], |E_{x∼Q}[(v · x)^ℓ] − E_{x∼P}[(v · x)^ℓ]| < ∆. 3. If every Hermite
moment tensor A_i = E_{x∼Q}[H_i(x)], i ∈ [k], satisfies ∥A_i∥_F ≤ H, the algorithm does not return
Reject."

**Formalization Note.**
* "Algorithm 2" is read as one `ArithmeticOnly` program of the `GaussMixHH` machine meeting its
  guarantee, chosen with one constant `C : ℕ` before all parameters and all `Q`: Algorithm 2 uses
  exact singular subspaces, which arithmetic does not compute. The program receives `d` in pointer
  `0` and `k, ∆, V, H` in memory (`finderInput`), and reaches `Q` only through `sample`.
* The `V`-assumption is `PolyMomentBound Q V k` (lower integrals). `O(·)`: samples at most
  `d^k C k^{Ck} V/∆²`, work at most `d^{Ck} exp(C k^{Ck} (H²/∆²) log(H/∆)) V^C`, on every sample
  stream; every run halts with a well-formed output.
* The output (`decodeFinder`): `r[0] = 0` Reject, `1` None, `2` a direction given by a nonzero vector
  `ŵ` in memory; the unit direction is `ŵ/∥ŵ∥` (the machine has no square root).
* "With probability at least 2/3": a measurable set of streams of measure at least `2/3` on which
  items 1–3 hold. `E_{x∼P}` is against `stdGaussian`; `F_ℓ` is `momentGap`. -/
theorem proposition_3_3 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P) (C : ℕ),
      ∀ (k d : ℕ), 1 ≤ k → 1 ≤ d → ∀ (Δ V H : ℝ), 0 < Δ → Δ < 1 / 2 → 1 ≤ V → 1 ≤ H →
      ∀ (Q : Measure (Vec d)) [IsProbabilityMeasure Q], PolyMomentBound Q V k →
        (∀ xs : ℕ → Vec d, ∃ t : ℕ,
          (GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H)) (noCoins, xs) t).halted
              = true ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H)) (noCoins, xs)
              t).samplesUsed : ℝ) ≤ (d : ℝ) ^ k * (C * (k : ℝ) ^ (C * k)) * V / Δ ^ 2 ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H)) (noCoins, xs)
              t).work : ℝ) ≤
            (d : ℝ) ^ (C * k) * Real.exp (C * (k : ℝ) ^ (C * k) * (H ^ 2 / Δ ^ 2) * Real.log (H / Δ)) *
              V ^ C ∧
          decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H))
            (noCoins, xs) t) ≠ none) ∧
        ∃ E : Set (ℕ → Vec d), MeasurableSet E ∧
          (2 / 3 : ENNReal) ≤ Measure.infinitePi (fun _ : ℕ => Q) E ∧
          ∀ xs ∈ E, ∀ t : ℕ,
            (GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H)) (noCoins, xs)
              t).halted = true →
            (∀ w : Vec d, decodeFinder d (GaussMixHH.run P d
                (GaussMixHH.initState d (finderInput k Δ V H)) (noCoins, xs) t) = some (.dir w) →
              ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k ∧ 3 * Δ / 8 ≤ |momentGap Q ℓ w|) ∧
            (decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H))
                (noCoins, xs) t) = some .none →
              ∀ v : Vec d, ‖v‖ = 1 → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → |momentGap Q ℓ v| < Δ) ∧
            ((∀ i : ℕ, 1 ≤ i → i ≤ k → frobeniusNorm (hermiteMoment Q i) ≤ H) →
              decodeFinder d (GaussMixHH.run P d (GaussMixHH.initState d (finderInput k Δ V H))
                (noCoins, xs) t) ≠ some .reject) := by sorry

end GaussPart
