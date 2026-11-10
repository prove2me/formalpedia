-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_3_2
-- name    : OptStochMatch.Tight.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:53:37.769814+00:00
-- url     : https://prove2.me/theorems/f48c66a3-5d73-4bee-be9b-97769814a1b7
-- title:
--   Lemma 3.2 — both offline optima via maximum deficiencies
-- statement:
--   For every realization of the type counts $N$ and of the service demands $z\ge0$,
--   $$\mathrm{OPT}^{\mathrm{Pois}}(N)=m-\max_{A\subseteq[m]}\delta^{\mathrm{Pois}}_N(A),\qquad \mathrm{OPT}^{\mathrm{Exp}}(z)=z([m])-\max_{A\subseteq[m]}\delta^{\mathrm{Exp}}_z(A).$$
--
--   Differences from the source:
--   - encoding: OPT^Pois(N) the LP maximum (integral by bipartite integrality) → optPois: sSup of the LP objective over the feasible set; reason: the feasible set is nonempty and compact, so the sSup is the LP maximum; the LP value itself is used, as printed
--   - encoding: every realization of the service demands → every z with z_i ≥ 0; reason: Exp(1) demands are nonnegative; for z with a negative coordinate the program has no feasible point
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 3.2, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 3.2 (p. 9, PDF 10). For every realization of the type counts `N` and of the
(nonnegative) service demands `z`,
`OPT^Pois(N) = m − max_{A ⊆ [m]} δ^Pois_N(A)` and
`OPT^Exp(z) = z([m]) − max_{A ⊆ [m]} δ^Exp_z(A)`. -/
theorem lemma_3_2 {m : ℕ} (lam : Ty m → ℝ≥0) :
    (∀ N : Ty m → ℕ, optPois N = (m : ℝ) - (maxDefPois N : ℝ)) ∧
    (∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → optExp lam z = ∑ i, z i - maxDefExp lam z) := by sorry

end OptStochMatch.Tight
