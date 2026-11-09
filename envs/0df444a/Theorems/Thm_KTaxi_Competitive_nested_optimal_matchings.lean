-- Prove2me | Theorems.Thm_KTaxi_Competitive_nested_optimal_matchings
-- name    : KTaxi.Competitive.nested_optimal_matchings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:59.689731+00:00
-- url     : https://prove2.me/theorems/12c23a7d-5cf2-48fc-a08c-114999594b3f
-- title:
--   §4.2 — optimal matchings $M_0=\emptyset,M_1,\dots,M_k$ by successive augmentation
-- statement:
--   For every online ordered list $x$ and every adversary configuration $Y$ there is an augmenting chain: matchings $M_0=\emptyset,M_1,\dots,M_k$ with each $M_m:X_m\hookrightarrow Y$ optimal, i.e. of cost $D(X_m,Y)$, and each $M_m$ obtained from $M_{m-1}$ by augmenting along one alternating path from the new taxi $x_m$ to an adversary taxi $y_m$ not used by $M_{m-1}$. In particular the images $Y_m=\{y_1,\dots,y_m\}$ form a nested sequence.
--
--   This is the successive-shortest-path property of minimum-cost bipartite matching. The analysis of §4.2–4.3 fixes such a chain and reads off the level $\ell$ at which the matching first uses the pickup $r$.
--
--   Differences from the source:
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - encoding: augment M_{m−1} along an augmenting path that minimizes the increase in matching cost, obtaining an optimal M_m → M_m optimal and obtained from M_{m−1} by exactly one alternating path ending at an unused adversary taxi; reason: for optimal M_{m−1} and M_m, the single augmenting path is one of minimum increase
--   - generalization: Y is an adversary configuration containing r → any adversary configuration Y; reason: the construction does not use r; the paper's case is an instance
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → every k : ℕ, including k = 0 and k = 1; reason: the finite matching construction applies unchanged; for k = 0 all prefixes are empty, and for k = 1 the chain adds the sole matching edge
--   - generalization: d_i > 0 for every taxi relative to the pickup r (§4.2 standing assumption) → no pickup or positivity assumption on x and Y; reason: successive augmentation uses only finite matching costs, including zero-cost edges; it does not use the pickup distances
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §4.2, PDF p. 8 (printed p. 7): "We fix an optimal matching M_m … The images Y_m form a nested sequence."

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **§4.2, nested optimal matchings** (PDF p. 8). For every online ordered list `x` and every
adversary configuration `Y` there is an augmenting chain: optimal matchings `M_0 = ∅, M_1, …,
M_k` of the prefixes `X_m` into `Y`, each `M_m` obtained from `M_{m-1}` by augmenting along one
alternating path from the new taxi `x_m` to an adversary taxi `y_m` unused by `M_{m-1}`; in
particular the images `Y_m = {y_1, …, y_m}` are nested. -/
theorem nested_optimal_matchings {V : Type*} [MetricSpace V] {k : ℕ} (x Y : Fin k → V) :
    ∃ M : ℕ → Fin k → Fin k, IsAugmentingChain x Y M := by sorry

end KTaxi.Competitive
