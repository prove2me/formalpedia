-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_theorem_3_4
-- name    : HolonomicPositivity.Robust.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:20.113594+00:00
-- url     : https://prove2.me/theorems/6a4a845d-6307-4a29-9544-f12b0a8298a8
-- title:
--   Theorem 3.4 — exact necessity on the negative-coefficient subclass
-- statement:
--   Let $P,Q\in\mathbb R(x)$ have no poles on $\mathbb N$, with $Q(n)\ne0$ for every $n\in\mathbb N$. Suppose $P<0+O(x^{-3})$ in the paper's strict comparison and $P\ge-1/4-1/(16x^2)+O(x^{-3})$ in its comparison modulo an error term. Let $p_0,p_1,p_2,p_3$ be the Taylor coefficients of $P$ at infinity, and let $R_P$ be the threshold of case (II-1). Then
--   $$\text{the normalized recurrence admits a robustly ultimately positive solution}\quad\Longleftrightarrow\quad Q(x)\ge R_P(x)+O(x^{-3}).$$
--   Robustness permits small independent perturbations of the three initial values, with $P,Q$ fixed. Both directions are asserted.
--
--   This companion theorem identifies an exact threshold on the stated subclass of recurrences.
--
--   Differences from the source:
--   - encoding: the Taylor coefficients of P used by the case (II-1) threshold → explicit p₀,p₁,p₂,p₃ with HasTaylorExpansion P p₀ p₁ p₂ p₃; reason: the assumptions bound P at infinity, so these coefficients exist and are uniquely determined; this names them without restricting P
--   - encoding: rational coefficients without natural poles and Q(N) excludes zero → NoPolesOnNat P and Q, and ∀ n, ev Q n ≠ 0; reason: spells out the global no-pole convention and the displayed nonvanishing assumption
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Theorem 3.4, PDF p.6 (printed 6); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Recurrence

namespace HolonomicPositivity.Robust.Supplement

/-- Theorem 3.4, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF p.6,
printed XX:6. The Taylor coefficients are tied to P by (7), rather than arbitrary parameters. -/
theorem theorem_3_4 (P Q : RatFunc ℝ)
    (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q) (hQ0 : ∀ n : ℕ, ev Q n ≠ 0)
    (hneg : LtMod (ev P) (fun _ => 0) (-3))
    (hsix : GeMod (ev P) (fun x => -(1 / 4) - 1 / (16 * x ^ 2)) (-3))
    (p₀ p₁ p₂ p₃ : ℝ) (hTaylor : HasTaylorExpansion P p₀ p₁ p₂ p₃) :
    AdmitsRobustlyUltimatelyPositiveSolution P Q ↔
      GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3) := by sorry

end HolonomicPositivity.Robust.Supplement
