-- Prove2me | Theorems.Thm_GaussPart_claim_3_18
-- name    : GaussPart.claim_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:12.372052+00:00
-- url     : https://prove2.me/theorems/d3d9ab19-26d6-43a7-bfda-2d4c337bf6a0
-- title:
--   Claim 3.18 — empirical Hermite tensors are $\tau$-accurate with probability $2/3$
-- statement:
--   Under the hypotheses of Proposition 3.3 ($d,k\ge1$, $V\ge1$, and $\mathbb E_Q[p^2]\le V\|p\|^2_{L^2(N(0,I_d))}$ for every polynomial of degree at most $k$), let $\tau\in(0,1)$ and $x^{(1)},\dots,x^{(n)}$ be i.i.d. from $Q$. If
--   $$n\ge\frac{3V(d+k)^k}{\tau^2},$$
--   then with probability at least $2/3$, simultaneously for every $i\in[k]$, $\|\hat A_i-A_i\|_F\le\tau$, where $A_i=\mathbb E_Q[\mathcal H_i]$ and $\hat A_i=\frac1n\sum_s\mathcal H_i(x^{(s)})$.
--
--   This is the single probabilistic event of the moment discrepancy finder.
--
--   **Formalization Note** The probability is the product measure $Q^{\otimes n}$; the event contains a measurable set of measure at least $2/3$.
--
--   Differences from the source:
--   - encoding: E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial of degree ≤ k → PolyMomentBound Q V k: lower Lebesgue integrals of p², polynomials MvPolynomial (Fin d) ℝ of total degree ≤ k; reason: a Bochner integral of a non-integrable p² would be 0 and make the assumption vacuous
--   - encoding: with probability at least 2/3 → a measurable set of samples of Q^{⊗n}-measure at least 2/3 on which all k bounds hold; reason: no outer measure
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Claim 3.18, p.31 (PDF p.33); hypotheses of Proposition 3.3, p.15

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Claim 3.18** (Empirical tensor estimation).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Claim 3.18, p.31 (PDF p.33), in the proof of
Proposition 3.3 (p.15), whose hypotheses it uses.

"If n ≥ 3V(d + k)^k/τ², with probability at least 2/3 we have simultaneously for every i ∈ [k] that
∥Â_i − A_i∥_F ≤ τ."

**Formalization Note.**
* Standing hypotheses of Proposition 3.3: `k, d ≥ 1`, `V ≥ 1`, and the `V`-assumption
  `PolyMomentBound Q V k` (`E_Q[p²] ≤ V∥p∥²_{L²(N(0,I_d))}` for every polynomial of total degree
  `≤ k`, in lower integrals). `τ ∈ (0, 1)` is the free parameter of p.31.
* `A_i = E_Q[H_i]` is `hermiteMoment Q i` and `Â_i` is `empiricalTensor xs i` for the sample
  `xs ∈ (ℝ^d)^n` drawn from `Q^{⊗n}`. "With probability at least 2/3": a measurable set of samples of
  measure at least `2/3` on which all `k` bounds hold. -/
theorem claim_3_18 {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (Q : Measure (Vec d))
    [IsProbabilityMeasure Q] (V : ℝ) (hV : 1 ≤ V) (hQ : PolyMomentBound Q V k) (τ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (n : ℕ) (hn : 3 * V * ((d : ℝ) + k) ^ k / τ ^ 2 ≤ n) :
    ∃ E : Set (Fin n → Vec d), MeasurableSet E ∧
      (2 / 3 : ENNReal) ≤ Measure.pi (fun _ : Fin n => Q) E ∧
      ∀ xs ∈ E, ∀ i : ℕ, 1 ≤ i → i ≤ k →
        frobeniusNorm (fun J => empiricalTensor xs i J - hermiteMoment Q i J) ≤ τ := by sorry

end GaussPart
