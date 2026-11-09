-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_corollary_C_2
-- name    : OnlineRealSampling.Exact.corollary_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:08.930348+00:00
-- url     : https://prove2.me/theorems/9c21aa3a-6ecf-4606-bc9c-cd049501d657
-- title:
--   Corollary C.2 — entropy is $O(\mathbb E[\log X])$
-- statement:
--   There is a universal constant $C$ such that for every random variable $X$ on $\mathbb N$ with PMF $f$,
--   $$H(X)=\mathbb E\Big[\lg\frac1{f(X)}\Big]\le C\,\mathbb E[\log X].\qquad(96)$$
--
--   No finiteness of the support, of the mean or of the entropy is assumed; both sides may be infinite. This is how the bounds in $\log(1/f(X_i))$ of Section 5 become bounds in $\log X_i$ in Theorem 1.2.
--
--   **Formalization Note** $X$ is given by its PMF $a_i=f(i)$, and expectations are sums in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: H(X) ≤ O(E[log X]) for a random variable X over ℕ → one constant C, PMF a ≥ 0 with Σ a = 1, both sides as sums in [0, ∞]; reason: the law of X is its PMF; the sums are the expectations
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Corollary C.2, PDF 21 / printed 20

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Oracle

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Corollary C.2. For every random variable `X` on `ℕ` with PMF `f`,
`H(X) = E[lg(1/f(X))] ≤ O(E[log X])`, with one universal constant (expectations in `[0, ∞]`). -/
theorem corollary_C_2 :
    ∃ C : ℝ, ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) → HasSum a 1 →
      ∑' i : ℕ, ENNReal.ofReal (a i * lg (1 / a i)) ≤
        ENNReal.ofReal C * ∑' i : ℕ, ENNReal.ofReal (a i * slog i) := by sorry

end OnlineRealSampling.Exact
