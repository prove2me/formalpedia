-- Prove2me | Theorems.Thm_NSWBetter_theorem_4_21
-- name    : NSWBetter.theorem_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:59:32.009942+00:00
-- url     : https://prove2.me/theorems/c2d2b98b-63cc-43a6-a3fa-ff52328c34e0
-- title:
--   Theorem 4.21 — ST rounding gains a constant when at least $\gamma^3n$ agents are not well-behaved
-- statement:
--   There is an absolute constant $c_1^*>0$ such that the following holds. Let $v\ge0$ be additive valuations, $y$ a configuration LP solution (rational, feasible, finite objective) and $x$ its corresponding fractional allocation. If at least $\gamma^3n$ agents are not well-behaved in $x$, then for every ST rounding scheme for $x$ (Marginals, Cardinality, Rationality),
--   $$\mathrm{ST}(x)\ge\frac1n\sum_{i\in N,S\subseteq G}y_{i,S}\ln v_i(S)-\frac1e+c_1^* .$$
--
--   Differences from the source:
--   - reading: "for some constant $c_1^*>0$" → one $c_1^*$ for all instances; reason: the constant is combined uniformly in the proof of Theorem 1.1; a per-instance constant would be weaker
--   - reading: "configuration LP solution" → rational, valid, finite objective; reason: the standing convention of p.19
--   - reading: $\mathrm{ST}(x)$ of the ST rounding algorithm → the bound for every value order and every scheme with Marginals, Cardinality and Rationality; reason: the source allows any such rounding and fixes the order only up to ties
--   - encoding: valuations $v_i:2^G\to\mathbb R_{\ge0}$ → `v : Fin n → Fin m → ℝ`, $v\ge0$; reason: Lean convention; same instances
--   - encoding: the random matching and $\mathrm{ST}(x)$ → a finitely supported distribution on matchings, `ST` in `EReal` with $\ln0=-\infty$; reason: same values whenever finite
--   - reading: "not well-behaved" (Definition 4.14, "for all feasible $\Delta$") → for every $\Delta\ge1$ with all $\Delta x_{ig}$ integral; reason: by Lemma 4.12 the same predicate for rational $x$
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 4.21, p.27

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_IsCLPSolution
import Definitions.Def_NSWBetter_lpVal
import Definitions.Def_NSWBetter_corrFrac
import Definitions.Def_NSWBetter_IsValueOrder
import Definitions.Def_NSWBetter_IsSTScheme
import Definitions.Def_NSWBetter_IsRationalScheme
import Definitions.Def_NSWBetter_ST
import Definitions.Def_NSWBetter_Nnwb

namespace NSWBetter

/-- **Theorem 4.21.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 4.21, p.27: "Let y be a configuration LP solution and let x be the corresponding fractional allocation. If at least γ³n agents are not well-behaved in x, then the following holds ST(x) ≥ (1/n) Σ_(i∈N,S⊆G) yi,S ln vi(S) − 1/e + c∗1 for some constant c∗1 > 0."

**Formalization Note.** One absolute constant `c₁`. `ST(x)` is bounded for every ST rounding scheme (Marginals, Cardinality, Rationality) built on any non-increasing value order. -/
theorem theorem_4_21 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (n m : ℕ) (v : Fin n → Fin m → ℝ), (∀ i g, 0 ≤ v i g) →
      ∀ y : Fin n → Finset (Fin m) → ℝ, IsCLPSolution v y →
      gamma ^ 3 * n ≤ ((Nnwb v (corrFrac y)).card : ℝ) →
      ∀ r : Fin n → Fin m ≃ Fin m, IsValueOrder v r →
      ∀ D : Finset (Fin n × Fin m × Fin m) → ℝ, IsSTScheme r (corrFrac y) D → IsRationalScheme D →
        ((lpVal v y - 1 / Real.exp 1 + c₁ : ℝ) : EReal) ≤ ST v D := by sorry

end NSWBetter
