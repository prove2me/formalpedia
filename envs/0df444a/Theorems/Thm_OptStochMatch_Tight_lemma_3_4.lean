-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_3_4
-- name    : OptStochMatch.Tight.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:54:14.174419+00:00
-- url     : https://prove2.me/theorems/4e00ff02-caf7-466b-a2f2-8728e822bf93
-- title:
--   Lemma 3.4 — Poisson–exponential duality on a chain
-- statement:
--   Fix a chain $\emptyset\neq A_1\subsetneq\cdots\subsetneq A_k\subseteq[m]$. For every $a\ge0$, with $K_a\sim\mathrm{Pois}(a)$ independent of $N$ ($N_S\sim\mathrm{Pois}(\lambda_S)$ independent) and $Z_i\sim\mathrm{Exp}(1)$ independent,
--   $$\mathbb P\big(\delta^{\mathrm{Exp}}_Z(A_r)>a\ \forall r\big)=\mathbb P\big(\delta^{\mathrm{Pois}}_N(A_r)>K_a\ \forall r\big).$$
--
--   Differences from the source:
--   - encoding: a ≥ 0 real, K_a independent of N → a : ℝ≥0, the product law countLaw λ ⊗ Pois(a); reason: same quantifier range and same joint law
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 3.4, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 3.4 (p. 10, PDF 11), Poisson–exponential duality on a chain. Fix a chain
`∅ ≠ A_1 ⊊ ⋯ ⊊ A_k ⊆ [m]`. For every `a ≥ 0`, with `K_a ∼ Pois(a)` independent of the type
counts `N` (`N_S ∼ Pois(λ_S)` independent) and with independent demands `Z_i ∼ Exp(1)`,
`P(δ^Exp_Z(A_r) > a ∀ r) = P(δ^Pois_N(A_r) > K_a ∀ r)`. -/
theorem lemma_3_4 {m : ℕ} (lam : Ty m → ℝ≥0) {k : ℕ} (hk : 0 < k)
    (c : Fin k → Finset (Fin m)) (hc : StrictMono c) (hne : ∀ r, (c r).Nonempty) (a : ℝ≥0) :
    demandLaw m {z | ∀ r, (a : ℝ) < defExp lam z (c r)} =
      ((countLaw lam).prod (poissonMeasure a)) {p | ∀ r, (p.2 : ℤ) < defPois p.1 (c r)} := by sorry

end OptStochMatch.Tight
