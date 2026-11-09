-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_deterministic_lower_bound
-- name    : OnlineThreeColorBounds.LowerBound.deterministic_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:44.991319+00:00
-- url     : https://prove2.me/theorems/ce4e6726-4ce0-43b7-9384-db78e237a8bb
-- title:
--   Theorem 1.1 — deterministic online coloring lower bound
-- statement:
--   There are an absolute real constant $c>0$ and a natural threshold $n_0$ such that, for every $n\ge n_0$ and every deterministic online coloring algorithm $A$, even if $A$ knows $n$, some ordered three-colorable graph $G$ on exactly $n$ vertices satisfies
--   $$
--   C_A(G,\pi)\ge 2^{c(\log_2 n)^{1/3}(\log_2\log_2 n)^{2/3}}.
--   $$
--   Here $C_A(G,\pi)$ is the number of distinct irrevocable online color names used in the recursively computed run, and three-colorable means admitting a proper coloring with at most three colors. The constants precede $n$, the algorithm, and the graph; the graph and its arrival order may depend on both $n$ and $A$. No computational bound, connectedness, bounded palette, or offline coloring certificate is imposed on $A$.
--
--   This is the complete deterministic lower bound of the pinned submission, not the size recurrence in its proof. The mathematical proof is supplied by §2.3; the Lean declaration remains an open proof target.
--
--   **Formalization Note** The carrier is $\operatorname{Fin}(n)$ in its natural arrival order, which encodes all finite ordered graphs by relabeling. The public horizon is an actual argument to the algorithm, while future adjacency is withheld. The threshold can be enlarged to at least four so both logarithms have positive arguments.
--
--   Differences from the source:
--   - encoding: finite ordered graphs and t-element online color sets → chronological lists of earlier-neighbor and natural-color finsets; the resulting graph has carrier Fin h.length; reason: arrival indices encode every finite order, and arbitrary finite color sets can be renamed into the unbounded natural palette
--   - encoding: immediate irrevocable decisions from revealed information, optionally knowing n → a function of past neighbor/color records and the new earlier neighbors, with a separate public horizon argument; reason: the complete past represents any deterministic internal state, with no future adjacency or offline certificate supplied
--   - generalization: a deterministic proper online coloring algorithm → properness required only on the algorithm's own runs on three-colorable graphs of exactly its public horizon n; reason: every source algorithm satisfies this; no requirement on other sizes, nonpromised graphs or unreachable histories excludes an algorithm
--   - encoding: for every sufficiently large n with the displayed logarithmic exponent → an existential natural threshold n0 at least four, base-two Real.logb and real fractional powers; reason: the threshold may be enlarged; §3.3 fixes base two and §2.3 uses it; real fractions preserve the exact exponent
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Theorem 1.1 and Remark 1.3(1), printed p. 1 / PDF p. 2; proof §2.3, printed pp. 9–10 / PDF pp. 10–11; logarithm convention §3.3, printed p. 13 / PDF p. 14

import Definitions.Def_OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Complete Theorem 1.1, printed p. 1 / PDF p. 2, with Remark 1.3(1).
The graph has exactly n arrival-indexed vertices and A receives the public horizon n.
Base-two logarithms follow §3.3; real exponents are real fractions. -/
theorem deterministic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ A : OnlineAlgorithm, ProperAt 1 3 n (A n) →
        ∃ G : SimpleGraph (Fin n), G.Colorable 3 ∧
          (2 : ℝ) ^ (c * (Real.logb 2 (n : ℝ)) ^ (1 / 3 : ℝ) *
            (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ (2 / 3 : ℝ)) ≤
              (colorCount (run (A n) G) : ℝ) := by sorry

end OnlineThreeColorBounds.LowerBound
