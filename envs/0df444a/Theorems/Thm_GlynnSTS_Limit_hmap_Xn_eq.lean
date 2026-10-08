-- Prove2me | Theorems.Thm_GlynnSTS_Limit_hmap_Xn_eq
-- name    : GlynnSTS.Limit.hmap_Xn_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:16:55.15393+00:00
-- url     : https://prove2.me/theorems/d41d7207-ac42-4853-b9b6-ab0fd77b795f
-- title:
--   Proof of Theorem 2.4, p. 3 — h(Xₙ) = (Ȳₙ(1) − μ)/g(Ȳₙ) by (2.3i) and (2.3ii)
-- statement:
--   Let $g : C[0,1] \to \mathbb R$ satisfy (2.3i), $g(\alpha x) = \alpha g(x)$ for $\alpha > 0$, and (2.3ii), $g(x - \beta k) = g(x)$ for $\beta \in \mathbb R$, where $k(t) = t$. Let $h(x) = x(1)/g(x)$ for $g(x) \ne 0$, $h(x) = 0$ otherwise, and $X_n = n^{1/2}(\bar Y_n - \mu k)$ for an arbitrary $C[0,1]$-valued $\bar Y_n$ and $\mu \in \mathbb R$. Then for every $n \ge 1$ and every $\omega$,
--   $$h(X_n) = \frac{n^{1/2}(\bar Y_n(1) - \mu)}{g\bigl(n^{1/2}(\bar Y_n - k\mu)\bigr)} = \frac{\bar Y_n(1) - \mu}{g(\bar Y_n - k\mu)} = \frac{\bar Y_n(1) - \mu}{g(\bar Y_n)}.$$
--
--   This converts the continuous-mapping step into the statement of Theorem 2.4: $h(X_n)$ is the standardized time average.
--
--   **Formalization Note** $n \ge 1$ is required because (2.3i) is applied with $\alpha = n^{1/2}$, which must be positive. Only (2.3i) and (2.3ii) are assumed; the identity is algebraic and holds for every $\bar Y_n$, so Assumption (2.1) is not needed. Where $g(\bar Y_n) = 0$ both sides are $0$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 3, proof of Theorem 2.4

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Limit

theorem hmap_Xn_eq {Ω : Type*} (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ : ℝ)
    (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x)
    (hshift : ∀ β : ℝ, ∀ x, g (x - β • kfun) = g x) :
    ∀ n : ℕ, 1 ≤ n → ∀ ω, hmap g (Xn Ybar μ n ω) = (Ybar n ω 1 - μ) / g (Ybar n ω) := by sorry

end GlynnSTS.Limit
