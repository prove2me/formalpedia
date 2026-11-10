-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_B_3
-- name    : GeoRobustLearn.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:40.141573+00:00
-- url     : https://prove2.me/theorems/2d5b3a9e-655b-45e8-bbe7-9ec1f1481ec3
-- title:
--   Lemma B.3 — sample implementation of LearnPolynomial in $(d+1)^{O(k)}\mathrm{poly}(\log 1/\delta)$ arithmetic operations
-- statement:
--   There are an arithmetic-only training program and universal constants $0<c_s\le1$, $0<c_\beta\le1/4$, $C_\beta\ge4$ (those of §4.3), $C_0>0$ and $C$ such that the following holds. Let $d\ge1$, $K\ge1$, $0<r\le1/K$, $\tau,\delta\in(0,1/4)$, and let $D$ be a distribution on $\mathbb R^d\times\{0,1\}$ with first marginal $\gamma$. Put
--
--   $$s=\frac{c_s\tau^2}{K^2},\qquad \beta=c_\beta Kr\,\sigma_s^2\,e^{-C_\beta r^2/s},\qquad k=\Big\lceil\frac1s\log\frac4{s\beta}\Big\rceil.$$
--
--   Then:
--
--   1. on every sample stream the program halts within $(d+1)^{Ck}(\log(2/\delta))^C$ steps, using at most that many samples and output reals;
--   2. with probability at least $1-\delta$ it returns a polynomial $P$ on $\mathbb R^{d+1}$ of degree at most $k$, and there is a polynomial $Q$ with $P=T_sQ$ and
--   $$\|Q\|_{L^2(\gamma_{d+1})}\le1,\quad \mathbb E_{(x,y)\sim D}|P(x,0)-y|\le\mathrm{opt}_K+C\tau,\quad m_P(r)-m_P(-r)\le C_0Kr,\quad \mathbb E_{(x,a)\sim\gamma_{d+1}}\mathrm{def}_Q(x,a)^2\le\beta.$$
--
--   This is the learning step of the main algorithm: it solves the convex program of Algorithm 1 from samples, in time essentially that of non-robust $L^1$ polynomial regression.
--
--   Differences from the source:
--   - reading: "there is an implementation of LearnPolynomial using samples" with "sample and real-arithmetic complexity" → ∃ one arithmetic-only program of the published real RAM (GeoLipLearn.Agnostic.Machine), chosen before all data, whose work, sample count and output length are bounded on every stream; reason: the paper counts samples and exact real-arithmetic operations (App. B, p.47); extra primitives would weaken the statement (paper.md decision 4)
--   - reading: "sufficiently small/large universal constants" c_s, c_β, C_β, C₀ → ∃ c_s ∈ (0,1], c_β ∈ (0,1/4], C_β ≥ 4, C₀ > 0 before all data; reason: the ranges printed on p.19; the constants are fixed by the paper's proof (paper.md decision 13)
--   - encoding: "returns a polynomial P of degree at most k" → the output block is the published dense monomial block of some degree k' ≤ k, decoded by coefficientFunction (d+1) k'; reason: a fixed finite representation of a polynomial; the block length determines k'
--   - encoding: P = T_sQ → equality of functions on Space (d+1) with the published ou s, plus Q.totalDegree ≤ k'; reason: T_s preserves degree, so the degree clause adds nothing
--   - encoding: O(τ) and (d+1)^{O(k)} poly(log 1/δ) → C·τ and (d+1)^{C·k}(log(2/δ))^C with one C before all data; reason: the meaning of O(·); log(2/δ) > 2 absorbs constants for δ < 1/4
--   - reading: "with probability at least 1 − δ" → a measurable event of mass ≥ 1 − δ under the stream law (HighProbability); reason: the published success-event convention; a stronger conclusion
--   - encoding: D a distribution on ℝ^d × {0, 1} whose first marginal is γ → a probability measure on Space d × ℝ with GaussianInput D and labels in {0, 1} D-a.s. (BinaryLabels); reason: Lean representation; same instances
--   - reading: d (dimension, unconstrained in the statement) → 1 ≤ d; reason: standing assumption of §5.1 (p.22); Theorem 6.1 is false at d = 0 (paper.md decision 6)
--   - encoding: E|P(x,0) − y| and opt_K → lower Lebesgue integral under D; opt_K over all of C_K with outer measures; reason: same values
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma B.3, p.50 (PDF p.50); parameters §4.3, p.19

import Definitions.Def_GeoLipLearn_Agnostic_Learner
import Definitions.Def_GeoRobustLearn_ArithmeticOnly
import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma B.3** (Sample implementation of the population learner), p.50.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There are one arithmetic-only training program `P`, universal constants `c_s ∈ (0, 1]`,
`c_β ∈ (0, 1/4]`, `C_β ≥ 4` (the constants of §4.3), `C₀ > 0` and a constant `C`, such that for
every `d ≥ 1`, `K ≥ 1`, `0 < r ≤ 1/K`, `τ, δ ∈ (0, 1/4)` and every distribution `D` on
`ℝ^d × {0, 1}` with first marginal `γ`, with `s = c_s τ²/K²`, `β = c_β K r σ_s² exp(−C_β r²/s)` and
`k = ⌈(1/s) log(4/(sβ))⌉` (§4.3 with `τ` in place of `ε`):
* on every stream, training halts within `(d+1)^{Ck} (log(2/δ))^C` steps, with at most that many
  samples and output reals;
* on a measurable event of probability at least `1 − δ`, the output is the monomial coefficient
  block of a polynomial `P̂` on `ℝ^{d+1}` of degree at most `k`, and there is a polynomial `Q` with
  `P̂ = T_s Q`, `‖Q‖_{L²(γ_{d+1})} ≤ 1`, `E_{(x,y)∼D}|P̂(x, 0) − y| ≤ opt_K + Cτ`,
  `m_{P̂}(r) − m_{P̂}(−r) ≤ C₀ K r` and `E_{(x,a)∼γ_{d+1}} def_Q(x, a)² ≤ β`.

**Formalization Note.** The output block of degree `k' ≤ k` is the published dense monomial block
(`coefficientFunction (d+1) k'`, length `(exponents (d+1) k').length`, which determines `k'`); "degree
at most `k`" is `k' ≤ k`. `P̂ = T_s Q` is equality of functions on `Space (d+1)` with the published
`ou s`. The sufficiently small/large universal constants are existential and chosen before all data.
`O(τ)` is `Cτ` and `(d+1)^{O(k)} poly(log 1/δ)` is `(d+1)^{Ck} (log(2/δ))^C`. The inputs `[K, r, τ, δ]`
are the first four memory cells. -/
theorem lemma_B_3 :
    ∃ (P : Program) (cs cβ Cβ C₀ : ℝ) (C : ℕ),
      Admissible P ∧ ArithmeticOnly P ∧
      0 < cs ∧ cs ≤ 1 ∧ 0 < cβ ∧ cβ ≤ 1 / 4 ∧ 4 ≤ Cβ ∧ 0 < C₀ ∧ 0 < C ∧
      ∀ (d : ℕ) (K r τ δ : ℝ) (D : Measure (Space d × ℝ)),
        1 ≤ d → IsProbabilityMeasure D → GaussianInput D → BinaryLabels D →
        1 ≤ K → 0 < r → r ≤ 1 / K → 0 < τ → τ < 1 / 4 → 0 < δ → δ < 1 / 4 →
        let s : ℝ := cs * τ ^ 2 / K ^ 2
        let β : ℝ := cβ * K * r * sigma s ^ 2 * Real.exp (-Cβ * r ^ 2 / s)
        let k : ℕ := ⌈(1 / s) * Real.log (4 / (s * β))⌉₊
        let R : ℝ := (d + 1 : ℝ) ^ (C * k) * (Real.log (2 / δ)) ^ C
        (∀ ω : Streams d, TrainingBudget (train P d 0 [K, r, τ, δ] R ω) R) ∧
        HighProbability (streamLaw D) δ (fun ω =>
          let rep := representation (train P d 0 [K, r, τ, δ] R ω)
          ∃ k' : ℕ, k' ≤ k ∧ rep.length = (exponents (d+1) k').length ∧
            let Phat : Space (d+1) → ℝ := coefficientFunction (d+1) k' rep
            ∃ Q : GeoLipLearn.Agnostic.Poly (d+1), Q.totalDegree ≤ k' ∧
              Phat = ou s (evalPoly Q) ∧
              normG 2 (evalPoly Q) ≤ 1 ∧
              ∫⁻ z, ENNReal.ofReal |Phat (lift z.1 0) - z.2| ∂D ≤ optK K D + ENNReal.ofReal (C * τ) ∧
              offsetMean Phat r - offsetMean Phat (-r) ≤ C₀ * K * r ∧
              ∫⁻ w, ENNReal.ofReal (certDefect (evalPoly Q) w ^ 2) ∂gaussian (d+1) ≤
                ENNReal.ofReal β) := by sorry

end GeoRobustLearn
