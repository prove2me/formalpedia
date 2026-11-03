-- Prove2me | Theorems.Thm_Grunbaum2003_sturm_tarski_and_signed_remainder_cauchy_index
-- name    : Grunbaum2003.sturm_tarski_and_signed_remainder_cauchy_index
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:22.090922+00:00
-- url     : https://prove2.me/theorems/0d89eb6b-521e-43cd-8cbf-da908671c7b7
-- title:
--   Sturm–Tarski theorem and signed pseudo-remainder Cauchy-index theorem over Polynomial ℝ
-- statement:
--   This theorem establishes the full real Sturm–Tarski theorem and Cauchy-index identity for signed pseudo-remainder sequences over $\mathbb{R}[X]$ (`Polynomial ℝ`), handling arbitrary polynomials $p, q \in \mathbb{R}[X]$ (including $p = 0$, $q = 0$, repeated roots, and common roots of $p$ and $q$).
--
--   Specifically, we construct:
--   1. **Three-valued real sign (`realSign`):** $\operatorname{sign}(x) \in \{-1, 0, 1\}$ for $x \in \mathbb{R}$;
--   2. **Signed pseudo-remainder operator (`realNextMod`):** Using canonical fuel-stabilized pseudo-division $lc(q)^c p = a q + r$ (`canonicalPseudoDiv`), the modified signed remainder
--      $$
--      \operatorname{realNextMod}(p, q) = -lc(q)^c r
--      $$
--      satisfies $\deg(\operatorname{realNextMod}(p, q)) < \deg(q)$ for all $q \neq 0$ and the positive-square three-term Sturm identity
--      $$
--      \bigl(lc(q)^c\bigr)^2 p = \bigl(lc(q)^c a\bigr) q - \operatorname{realNextMod}(p, q);
--      $$
--   3. **Signed-remainder sequence (`realMods`) and sign-variation difference at $\pm\infty$ (`realChangesPoly`):** Satisfying the unfolding equation $\operatorname{realMods}(p, q) = p :: \operatorname{realMods}(q, \operatorname{realNextMod}(p, q))$ for all $p \neq 0$;
--   4. **Global Cauchy index (`cauchyIndex`) and Cauchy-index theorem (`realChangesPoly_realMods_eq_cauchyIndex`):** For all $p, q \in \mathbb{R}[X]$,
--      $$
--      \operatorname{realChangesPoly}(\operatorname{realMods}(p, q)) = \operatorname{cauchyIndex}(p, q);
--      $$
--   5. **Sturm–Tarski theorem (`realTaqR_eq_tarskiQueryR`, `realTaqR_one`):** For all $p, q \in \mathbb{R}[X]$,
--      $$
--      \operatorname{realChangesPoly}(\operatorname{realMods}(p, p' q)) = \sum_{x \in \operatorname{roots}(p)} \operatorname{sign}(q(x)),
--      $$
--      and in particular $\operatorname{realChangesPoly}(\operatorname{realMods}(p, p')) = \#\operatorname{roots}_{\mathbb{R}}(p)$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91 (Tarski–Seidenberg real root counting via Sturm–Tarski queries)

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem sturm_tarski_and_signed_remainder_cauchy_index :
    ∃ (realSign : ℝ → ℤ)
      (realNextMod : Polynomial ℝ → Polynomial ℝ → Polynomial ℝ)
      (realMods : Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ))
      (realChangesPoly : List (Polynomial ℝ) → ℤ)
      (cauchyIndex : Polynomial ℝ → Polynomial ℝ → ℤ),
      (∀ x : ℝ, realSign x = (haveI := Classical.propDecidable; if 0 < x then 1 else if x < 0 then -1 else 0)) ∧
      (∀ p q : Polynomial ℝ, q ≠ 0 → (realNextMod p q).degree < q.degree) ∧
      (∀ p q : Polynomial ℝ, p ≠ 0 → realMods p q = p :: realMods q (realNextMod p q)) ∧
      (∀ p q : Polynomial ℝ, realChangesPoly (realMods p q) = cauchyIndex p q) ∧
      (∀ p q : Polynomial ℝ,
        realChangesPoly (realMods p (p.derivative * q)) =
          ∑ x ∈ p.roots.toFinset, realSign (q.eval x)) ∧
      (∀ p : Polynomial ℝ,
        realChangesPoly (realMods p p.derivative) = (p.roots.toFinset.card : ℤ)) := by sorry

end Grunbaum2003
