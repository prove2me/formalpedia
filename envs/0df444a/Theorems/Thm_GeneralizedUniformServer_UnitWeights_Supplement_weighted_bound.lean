-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_Supplement_weighted_bound
-- name    : GeneralizedUniformServer.UnitWeights.Supplement.weighted_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:14.349791+00:00
-- url     : https://prove2.me/theorems/dd3ae033-a997-419f-b5e4-8970ffcbc602
-- title:
--   Theorem 1.3 — a randomized algorithm with $\mathbb E[\mathrm{ALG}(\rho)]\le 20^k\,\mathrm{OPT}(\rho)+10^k w_k$ on weighted uniform metrics
-- statement:
--   Let $k\ge1$ and let $M_1,\dots,M_k$ be uniform metric spaces of arbitrary cardinality in which distinct points of $M_i$ are at distance $w_i$, where
--   $$0\le w_1\le w_2\le\cdots\le w_k .$$
--   Moving the servers from $x$ to $y$ costs $d_w(x,y)=\sum_i w_i\mathbf 1[x_i\ne y_i]$; a request is a tuple $r\in X=M_1\times\cdots\times M_k$, served by $x$ if $x_i=r_i$ for some $i$. Let $a\in X$ be an initial configuration. Then there is a randomized online algorithm, starting at $a$ and always moving to a configuration that serves the current request, such that for every finite request sequence $\rho$,
--   $$\mathbb E[\mathrm{ALG}(\rho)]\le 20^k\cdot\mathrm{OPT}(\rho)+10^k\,w_k,$$
--   where $\mathrm{ALG}(\rho)$ and $\mathrm{OPT}(\rho)$ are measured in $d_w$ and $\mathrm{OPT}(\rho)$ is the cost of an optimal offline solution starting from $a$.
--
--   The constants depend neither on the number of points nor on the ratios between the weights. Combined with the lower bound $\Omega(2^k)$ of Ayyadevara and Chiplunkar, it shows that the randomized competitive ratio on weighted uniform metrics is $\exp(\Theta(k))$.
--
--   **Formalization Note** The algorithm may depend on the spaces, the weights and $a$, but not on $\rho$; it ranges over the general history-dependent class of randomized online algorithms. Weights are nonnegative reals (`ℝ≥0`) with `Monotone w`; zero weights are allowed. $w_k$ is the weight of the last server, `w ⟨k-1, _⟩`. Costs and expectations are in $[0,\infty]$; $\mathrm{OPT}$ is the infimum over all offline solutions from $a$, which is attained (a minimum) and finite for $k\ge1$.
--
--   Differences from the source:
--   - encoding: real weights with 0 ≤ w_1 ≤ … ≤ w_k → w : Fin k → ℝ≥0 with Monotone w; reason: the same set of weight vectors.
--   - encoding: real-valued costs and expectation → values in ENNReal, OPT_w an infimum over offline solutions; reason: all quantities are nonnegative and finite for k ≥ 1, and the infimum is attained, so the inequality is the same.
--   - encoding: pairwise disjoint uniform metric spaces indexed by 1 through k → dependent coordinate types indexed by Fin k, with coordinate movement costs defined explicitly; reason: tagging each coordinate makes the spaces disjoint, and shifting the index labels changes no configuration, request, or cost.
--   - encoding: existence of a randomized online algorithm → existence of history-dependent PMF kernels serving on every history; reason: the source algorithm uses finite random choices on each finite prefix and has a behavioral PMF representation; returning the current request on unreachable histories preserves its law.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 3, Theorem 1.3 (model §2, pp. 7–8; proof §5, pp. 16–22)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Weighted

open scoped NNReal

namespace GeneralizedUniformServer.UnitWeights.Supplement

/-- Theorem 1.3 (source p. 3): let `M₁, …, M_k` (`k ≥ 1`) be uniform metric spaces in which
distinct points of `Mᵢ` are at distance `wᵢ`, where `0 ≤ w₁ ≤ ⋯ ≤ w_k`, and let `a` be an initial
configuration. There is a randomized online algorithm, which always moves to a configuration
serving the current request, such that for every finite request sequence `ρ`,
`E[ALG(ρ)] ≤ 20^k · OPT(ρ) + 10^k · w_k`. Here `w_k` is the weight of the last server. -/
theorem weighted_bound {k : ℕ} [NeZero k] {M : Fin k → Type*} (w : Fin k → ℝ≥0)
    (hw : Monotone w) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k * ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by sorry

end GeneralizedUniformServer.UnitWeights.Supplement
