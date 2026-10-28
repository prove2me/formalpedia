-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_log_sub_ge_of_integral_limits_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:16.967439+00:00
-- url     : https://prove2.me/theorems/8c2c9203-7701-486b-b236-68a42ba9b8b5
-- title:
--   Limit Assembly for Logarithmic Mass Comparison
-- statement:
--   This is an auxiliary limit-assembly statement related to Proposition 12 of Cordero–Klartag (arXiv:1304.0630v1).
--
--   Let $a:\mathbb{N}\to[0,\infty]$, $m:\mathbb{N}\to\mathbb{R}$, $Z\in[0,\infty]$, and $r,S,M\in\mathbb{R}$. Assume:
--
--   1. $0\le m_j$ for every $j$.
--   2. $\log a_j-m_j$ converges in the extended real line to $S$.
--   3. $m_j$ converges to $M$.
--   4. $\operatorname{ofReal}(r)\le\liminf_j\operatorname{ofReal}(m_j)$ in $[0,\infty]$.
--   5. $\limsup_j a_j\le Z$.
--
--   Then $Z>0$ and
--
--   $$
--   S\le \log Z-r.
--   $$
--
--   The declaration is a technical assembly lemma for passing from sequence limits and liminf/limsup bounds to a functional comparison; it is not an attainment statement.
--
--   **Formalization Note.** The quantities involving $a_j$ and $Z$ use `ENNReal.log`, while the subtraction and the comparison with $S$ and $r$ take place in `EReal`; the conclusion is expressed with the corresponding coercions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem log_sub_ge_of_integral_limits
--       (a : ℕ → ℝ≥0∞) (m : ℕ → ℝ) (Z : ℝ≥0∞) (r S M : ℝ)
--       (hnn : ∀ j, 0 ≤ m j)
--       (hF : Tendsto (fun j => ENNReal.log (a j) - (m j : EReal)) atTop (𝓝 (S : EReal)))
--       (hm : Tendsto m atTop (𝓝 M))
--       (hfirst : ENNReal.ofReal r ≤ liminf (fun j => ENNReal.ofReal (m j)) atTop)
--       (hsecond : limsup a atTop ≤ Z) :
--       0 < Z ∧ (S : EReal) ≤ ENNReal.log Z - (r : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Previous: [`limsup_mass_legendre_le`](https://prove2.me/theorems/a6e9fd8e-5a77-41be-9761-9a4957084c5b) · Next: [`real_legendre_normalization`](https://prove2.me/theorems/c3394fe1-6941-4e93-a4a1-c77d84338af6).
--
--   [Source excerpt, lines 211–218](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L211-L218) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L206-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open scoped ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter

theorem FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_readable
    (a : ℕ → ℝ≥0∞) (m : ℕ → ℝ) (Z : ℝ≥0∞) (r S M : ℝ)
    (hnn : ∀ j, 0 ≤ m j)
    (hF : Tendsto (fun j => ENNReal.log (a j) - (m j : EReal)) atTop (𝓝 (S : EReal)))
    (hm : Tendsto m atTop (𝓝 M))
    (hfirst : ENNReal.ofReal r ≤ liminf (fun j => ENNReal.ofReal (m j)) atTop)
    (hsecond : limsup a atTop ≤ Z) :
    0 < Z ∧ (S : EReal) ≤ ENNReal.log Z - (r : EReal) := by sorry
