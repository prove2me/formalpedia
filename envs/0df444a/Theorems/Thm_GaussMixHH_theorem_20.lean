-- Prove2me | Theorems.Thm_GaussMixHH_theorem_20
-- name    : GaussMixHH.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:54.641269+00:00
-- url     : https://prove2.me/theorems/52463fcb-6ef8-4922-b933-a332d4e52465
-- title:
--   Theorem 20, p.25 — algorithmic near-mass estimation with $e^{CA}\log(C/\zeta)$ samples and $e^{CA}\mathrm{polylog}(1/\zeta)$ time
-- statement:
--   There are one program $P$ of the sampling real RAM and constants $C>0$, $K\in\mathbb N$ such that the following holds. Let $0<R\le1$, $0<\eta<1/4$, $0<\zeta<1/3$, $n\ge C\log^2(1/\eta)/R^2$, $z\in\mathbb R^n$, and let $D$ be a probability measure on $\mathbb R^n$ whose radial law $\rho_z$ (the law of $\|\mu-z\|$, $\mu\sim D$) is $(R/2,R)$-gapped. Put
--
--   $$A=\frac{n^{1/3}\log^{4/3}(1/\eta)}{R^{4/3}} .$$
--
--   Run $P$ on input $(n;R,\eta,\zeta,z)$ with fair coins and i.i.d. samples from $D*N(0,I_n)$. Then:
--
--   1. on every coin tape and sample stream, $P$ halts after at most $e^{CA}\log(C/\zeta)$ samples and at most $e^{CA}\log^K(1/\zeta)$ steps;
--   2. its output $\hat m$ always lies in $[0,1]$;
--   3. with probability at least $1-\zeta$,
--   $$|\hat m-\operatorname{near-mass}_R(\rho_z)|<\eta .$$
--
--   The theorem estimates how much center weight lies within $R/2$ of $z$, provided no center lies at distance strictly between $R/2$ and $R$; Theorem 1 follows by thresholding.
--
--   Differences from the source:
--   - reading: "there is an algorithm", running time in "the real arithmetic model" (p.15) → one Admissible program of GaussMixHH.Machine (rational literals, √, exp, cos, sin, coins, sample of cost n), chosen with C, K before all parameters; reason: the paper names no instruction set; this is the weakest model its runtime count (p.28) uses
--   - encoding: B, A "the parameters from Proposition 19" with B = Θ(log²(1/η)/R²), A = Θ(n^{1/3} log^{4/3}(1/η)/R^{4/3}) → n ≥ C·log²(1/η)/R² and A = n^{1/3}·log^{4/3}(1/η)/R^{4/3}; reason: the explicit Θ forms printed in the statement; constant factors are absorbed into C
--   - encoding: polylog(1/ζ) → log(1/ζ)^K with K fixed; reason: log(1/ζ) > 1 for ζ < 1/3
--   - reading: sample complexity and running time "at most" → worst-case bounds on every coin tape and sample stream; reason: the proof's H, N, M and solver iteration count are deterministic
--   - reading: "returns m̂ ∈ [0, 1] satisfying |m̂ − near-mass| < η with probability at least 1 − ζ" → m̂ ∈ [0, 1] on every halted run; accuracy on a measurable set of probability ≥ 1 − ζ; reason: m̂ is the near mass of a probability vector; the stronger reading
--   - generalization: D the separated discrete center distribution → any Borel probability measure D on ℝⁿ with ρ_z gapped; reason: the proof uses neither separation nor atomicity
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 20, p.25 (PDF p.27); proof pp.26–28

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussMixHH_CenterModel
import Definitions.Def_GaussMixHH_Gapped

open MeasureTheory ProbabilityTheory

namespace GaussMixHH

/-- **Theorem 20** (Algorithmic near-mass estimation).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 20, p.25 (PDF p.27).

"Let 0 < R ≤ 1, 0 < η < 1/4, and 0 < ζ < 1/3. Fix a candidate point z ∈ Rn, and suppose that the
radial probability distribution ρz of ∥μ − z∥ is (R/2, R)-gapped. Let B, A be the parameters from
Proposition 19, so that B = Θ(log²(1/η)/R²), A = Θ(n^{1/3} log^{4/3}(1/η)/R^{4/3}). Suppose n ≥ CB.
Then there is an algorithm that returns m̂ ∈ [0, 1] satisfying |m̂ − near-mass_R(ρz)| < η, with
probability at least 1 − ζ. Its sample complexity is at most e^{CA} log(C/ζ), and its running time is
at most e^{CA} polylog(1/ζ)."

**Formalization Note.**
* "There is an algorithm": one `Admissible` program `P` of the sampling real RAM
  (`GaussMixHH.Machine`), chosen with `C` and the polylog degree `K` before all parameters, run on
  the layout `theorem20Input` (`n`; `R, η, ζ, z`) with output `m̂ = r[0]`. `P` sees the mixture only
  through `sample`.
* `B, A` are written in the explicit `Θ` forms the statement prints, `B = log²(1/η)/R²` and
  `A = n^{1/3} log^{4/3}(1/η)/R^{4/3}`; Proposition 19's `B, A` lie within constant factors of them,
  which `C` absorbs. `polylog(1/ζ)` is `log(1/ζ)^K` (`log(1/ζ) > 1` as `ζ < 1/3`).
* Sample and time bounds hold for every coin tape and sample stream; `m̂ ∈ [0, 1]` holds on every
  halted run; accuracy holds on a measurable set of probability at least `1 − ζ` under
  `sampleSpace D` (fair coins × i.i.d. samples of `Mix(D, 1)`).
* Generalization: `D` is any Borel probability measure on `ℝⁿ` whose radial law at `z` is gapped;
  the paper's proof uses neither separation nor atomicity. -/
theorem theorem_20 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) (R η ζ : ℝ), 0 < R → R ≤ 1 → 0 < η → η < 1 / 4 → 0 < ζ → ζ < 1 / 3 →
        C * Real.log (1 / η) ^ 2 / R ^ 2 ≤ n →
        ∀ (z : EuclideanSpace ℝ (Fin n)) (D : Measure (EuclideanSpace ℝ (Fin n)))
          [IsProbabilityMeasure D], IsGapped R (radialLaw D z) →
          let A := (n : ℝ) ^ ((1 : ℝ) / 3) * Real.log (1 / η) ^ ((4 : ℝ) / 3) / R ^ ((4 : ℝ) / 3)
          (∀ ω, ∃ t, (run P n (theorem20Input n R η ζ z) ω t).halted = true ∧
            ((run P n (theorem20Input n R η ζ z) ω t).samplesUsed : ℝ) ≤
              Real.exp (C * A) * Real.log (C / ζ) ∧
            ((run P n (theorem20Input n R η ζ z) ω t).work : ℝ) ≤
              Real.exp (C * A) * Real.log (1 / ζ) ^ K) ∧
          (∀ ω t, (run P n (theorem20Input n R η ζ z) ω t).halted = true →
            output (run P n (theorem20Input n R η ζ z) ω t) ∈ Set.Icc (0 : ℝ) 1) ∧
          ∃ E, MeasurableSet E ∧ 1 - ζ ≤ (sampleSpace D E).toReal ∧
            ∀ ω ∈ E, ∀ t, (run P n (theorem20Input n R η ζ z) ω t).halted = true →
              |output (run P n (theorem20Input n R η ζ z) ω t) - nearMass R (radialLaw D z)| < η := by sorry

end GaussMixHH
