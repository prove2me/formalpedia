-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_8
-- name    : OnlineMatchFrameworks.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:29:24.167691+00:00
-- url     : https://prove2.me/theorems/dbc31573-f965-486a-a186-176602e0764a
-- title:
--   Theorem 8: the LP (1a)–(1c) has stochasticity gap at most $2-2\gamma-\gamma^2\approx0.544$
-- statement:
--   Let $\gamma$ be the solution of $\gamma=e^{-\gamma}$ and let $\mathrm{LP}(G)$ be the value of LP (1) with the constraints (1a)–(1c) only. For every $\varepsilon>0$ there is a vertex-weighted instance $G$ with known patience values $\theta_v$ such that $\mathrm{LP}(G)>0$ and
--
--   $$
--   \mathrm{OPT}(G)\ \le\ (2-2\gamma-\gamma^2+\varepsilon)\,\mathrm{LP}(G),
--   $$
--
--   where $\mathrm{OPT}(G)$ is the offline sequential probing optimum. The constant $2-2\gamma-\gamma^2=0.54406\ldots$ is the paper's "$\approx0.544$". So no analysis that compares with this LP can prove a ratio above it, even for an offline algorithm.
--
--   Differences from the source:
--   - reading: ≈0.544 → 2 − 2γ − γ² with γ = e^{−γ}; reason: this is the number the proof obtains (p.54) and abbreviates; the decimal 0.544 is slightly smaller
--   - reading: a stochasticity gap of at most ≈0.544 → for every ε > 0 an instance with LP > 0 and OPT ≤ (constant + ε)·LP; reason: the gap is the infimum of OPT/LP over instances, approached as n → ∞ in the proof
--   - reading: the right side E[θ_v] of (1c), with no patience model named in the theorem → the witness has deterministic patience θ_v, so E[θ_v] = θ_v; reason: p.30 introduces this LP for "(known) patience constraints" and the proof’s instance has no random patience; allowing random patience in the witness would give a gap of 0 for an unrelated reason, so this is the stronger reading
--   - reading: no online or offline algorithm (p.54); the offline optimum (p.31) → the published OPT: adaptive offline probing trees that choose their own order; reason: the benchmark of p.12; a larger OPT makes the upper bound stronger
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 8, p.31; constant from Appendix A, proof of Theorem 8, p.54

import Definitions.Def_OnlineMatchFrameworks_Supplement_StandardLP
import Definitions.Def_OnlineMatchFrameworks_Offline
import Definitions.Def_OnlineMatchFrameworks_PatienceModels

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 8.** arXiv:1907.03963v6, Theorem 8, p.31: "The LP given by the objective function (1) and
constraints (1a)–(1c) has a stochasticity gap of at most ≈0.544."

**Formalization Note.** The constant behind "≈0.544" is `2 - 2γ - γ²` with `γ = e^{-γ}` (proof, p.54).
A gap of at most that constant means: for every `ε > 0` some instance with known patience values `θ v`
has a positive LP value and `OPT(G) ≤ (2 - 2γ - γ² + ε) · LP(G)`, with the published offline `OPT`. The
budget of (1c) is then `tailBudget (deterministicTail θ) v = θ v`. Patience is known, as §6.1 says ("a
standard LP relaxation for bipartite matching with (known) patience constraints", p.30); with a random
patience the budget `E[θ_v]` alone would push the ratio to `0`, for reasons unrelated to the random
graphs of the proof. -/
theorem theorem_8 :
    ∃ γ : ℝ, γ = Real.exp (-γ) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (a b : ℕ) (G : OnlineMatchFrameworks.Instance (Fin a) (Fin b)) (θ : Fin b → ℕ),
          (∀ v l, G.surv v l =
            OnlineMatchFrameworks.tailSurvival (OnlineMatchFrameworks.deterministicTail θ) v l) ∧
          0 < standardLPValue G
            (OnlineMatchFrameworks.tailBudget (OnlineMatchFrameworks.deterministicTail θ)) ∧
          G.OPT ≤ (2 - 2 * γ - γ ^ 2 + ε) * standardLPValue G
            (OnlineMatchFrameworks.tailBudget (OnlineMatchFrameworks.deterministicTail θ)) := by sorry

end OnlineMatchFrameworks.Supplement
