-- Prove2me | Theorems.Thm_OptStochMatch_Tight_theorem_5_5
-- name    : OptStochMatch.Tight.theorem_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:56:51.280273+00:00
-- url     : https://prove2.me/theorems/accdfc70-c1d8-4778-ba50-cc41e86cc484
-- title:
--   Theorem 5.5 — the policy associated with (5.8) is (1 − e^{1−e})-competitive; CRiid = 1 − e^{1−e}
-- statement:
--   For every $m$, $n\ge1$ and neighbourhood law $\mu$, the matching policy associated with the rule (5.8) exists, and every such policy has expected matching size at least $(1-e^{1-e})\,\mathrm{OPT}_n$. Hence $\mathrm{CR}_{\mathrm{iid}}=1-e^{1-e}$.
--
--   Differences from the source:
--   - reading: 'the matching policy associated with (5.8)' → existence of an associated policy, and the bound for every associated policy (any type-flow decomposition, any measurable choice); reason: the definite article presupposes existence (the trajectory is the solution of a Lipschitz ODE, p. 25); the decomposition is not unique and the source's argument does not depend on its choice
--   - encoding: online policies: decisions from the current arrival, the history and independent internal randomization → PoissonPolicy / IIDPolicy: one Uniform[0,1] seed and a decision map measurable in the seed and arrival times; reason: a single uniform seed generates any independent internal randomness; past decisions are functions of the seed and past arrivals; same policy class
--   - encoding: CR and CRiid as inf over instances with OPT > 0 of sup over algorithms knowing the instance → real sInf over instances (m, λ) resp. (n ≥ 1, m, µ with ∑µ = 1) with OPT > 0 of real sSup of ALG/OPT over policies of that instance; reason: the inner sets are nonempty and bounded (ALG ≤ m), the outer set is nonempty and bounded below by 0, so sInf/sSup are the source's inf/sup
--   - encoding: the continuous ODE service trajectories of (5.8), §5.3 → the accumulated-work integral equation with interval-integrable rates on each phase; reason: the source constructs continuous trajectories from its Lipschitz rate map; explicit integrability prevents the total Bochner integral from standing for undefined service
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Theorem 5.5, p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Algorithms
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Theorem 5.5 (p. 25, PDF 26). For every `m`, `n ≥ 1` and neighbourhood law `µ`, the
matching policy associated with the rule (5.8) exists and every such policy has expected
matching size at least `(1 − e^{1−e}) OPT_n`. Hence `CRiid = 1 − e^{1−e}`. -/
theorem theorem_5_5 :
    (∀ (m n : ℕ) (mu : Ty m → ℝ≥0), 1 ≤ n → ∑ S, mu S = 1 →
      (∃ ρ : RoutingRule m, IsAssoc58 n mu ρ) ∧
      ∀ ρ : RoutingRule m, IsAssoc58 n mu ρ → cStar * optIID n mu ≤ algRouteIID n mu ρ) ∧
    CRiid = cStar := by sorry

end OptStochMatch.Tight
