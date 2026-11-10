-- Prove2me | Theorems.Thm_OptStochMatch_Tight_theorem_3_1
-- name    : OptStochMatch.Tight.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:54:29.629063+00:00
-- url     : https://prove2.me/theorems/10e9c71b-8086-44f8-a68a-d70f73ef221b
-- title:
--   Theorem 3.1 — offline equality E[OPT^Pois(N)] = E[OPT^Exp(Z)]
-- statement:
--   For Poisson matching with intensity vector $\lambda$ and scheduling with feasible-rate region $\mathcal P_\lambda$ and $\mathrm{Exp}(1)$ demands, $\mathbb E[\mathrm{OPT}^{\mathrm{Pois}}(N)]=\mathbb E[\mathrm{OPT}^{\mathrm{Exp}}(Z)]$.
--
--   Differences from the source:
--   - encoding: OPT^Pois(N) the LP maximum (integral by bipartite integrality) → optPois: sSup of the LP objective over the feasible set; reason: the feasible set is nonempty and compact, so the sSup is the LP maximum; the LP value itself is used, as printed
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Theorem 3.1, p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Theorem 3.1 (p. 8, PDF 9), offline Poisson–exponential duality. For Poisson matching with
intensity vector `λ` and scheduling with feasible-rate region `P_λ` and `Exp(1)` service
demands, `E[OPT^Pois(N)] = E[OPT^Exp(Z)]`. -/
theorem theorem_3_1 {m : ℕ} (lam : Ty m → ℝ≥0) :
    ∫ N, optPois N ∂(countLaw lam) = ∫ z, optExp lam z ∂(demandLaw m) := by sorry

end OptStochMatch.Tight
