-- Prove2me | Theorems.Thm_OptStochMatch_Tight_proposition_3_5
-- name    : OptStochMatch.Tight.proposition_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:54:22.19205+00:00
-- url     : https://prove2.me/theorems/6886ba21-b434-4781-b977-a22c30ccf4a7
-- title:
--   Proposition 3.5 — distributional identity between the two maximum deficiencies
-- statement:
--   (3.1) For every $a\ge0$, with $K_a\sim\mathrm{Pois}(a)$ independent of $N$: $\mathbb P(\max_A\delta^{\mathrm{Exp}}_Z(A)>a)=\mathbb P(\max_A\delta^{\mathrm{Pois}}_N(A)>K_a)$. (3.2) With independent $E_1,E_2,\ldots\sim\mathrm{Exp}(1)$ independent of $N$, and the empty sum zero, $\max_A\delta^{\mathrm{Exp}}_Z(A)\overset{d}{=}\sum_{\ell=1}^{\max_A\delta^{\mathrm{Pois}}_N(A)}E_\ell\sim\mathrm{Gamma}(\max_A\delta^{\mathrm{Pois}}_N(A),1)$.
--
--   Differences from the source:
--   - encoding: E_1, E_2, … independent Exp(1) → E_0, …, E_{m−1} (a vector with law demandLaw m); reason: 0 ≤ max_A δ^Pois_N(A) ≤ m, so only the first m variables enter the sum; same law
--   - encoding: Gamma(M, 1) with random integer shape M ≥ 0 → the mixture ∑_k P(M = k)·Gamma(k, 1), with Gamma(0, 1) the point mass at 0; reason: the source's empty-sum convention; the law of a Gamma variable with random shape is this mixture
--   - encoding: equality in distribution → equality of pushforward measures; reason: same notion
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Proposition 3.5, eqs. (3.1)–(3.2), p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Proposition 3.5 (p. 12, PDF 13). (3.1): for every `a ≥ 0`, with `K_a ∼ Pois(a)` independent
of `N`, `P(max_A δ^Exp_Z(A) > a) = P(max_A δ^Pois_N(A) > K_a)`. (3.2): with independent
`E_1, E_2, … ∼ Exp(1)` independent of `N` (the empty sum being zero),
`max_A δ^Exp_Z(A) =ᵈ ∑_{ℓ=1}^{max_A δ^Pois_N(A)} E_ℓ ∼ Gamma(max_A δ^Pois_N(A), 1)`, where
`Gamma(0, 1)` is the point mass at `0`. Since `0 ≤ max_A δ^Pois_N(A) ≤ m`, only `E_1, …, E_m`
enter the sum; they are indexed `0, …, m − 1`. -/
theorem proposition_3_5 {m : ℕ} (lam : Ty m → ℝ≥0) :
    (∀ a : ℝ≥0, demandLaw m {z | (a : ℝ) < maxDefExp lam z} =
      ((countLaw lam).prod (poissonMeasure a)) {p | (p.2 : ℤ) < maxDefPois p.1}) ∧
    (demandLaw m).map (maxDefExp lam) =
      ((countLaw lam).prod (demandLaw m)).map (fun p =>
        ∑ l ∈ (Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois p.1), p.2 l) ∧
    ((countLaw lam).prod (demandLaw m)).map (fun p =>
        ∑ l ∈ (Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois p.1), p.2 l) =
      Measure.sum (fun k : ℕ => countLaw lam {N | maxDefPois N = (k : ℤ)} •
        (if k = 0 then Measure.dirac (0 : ℝ) else gammaMeasure (k : ℝ) 1)) := by sorry

end OptStochMatch.Tight
