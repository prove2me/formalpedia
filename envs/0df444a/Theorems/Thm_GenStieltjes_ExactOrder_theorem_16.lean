-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_theorem_16
-- name    : GenStieltjes.ExactOrder.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:38.10826+00:00
-- url     : https://prove2.me/theorems/c239a681-4096-4f50-af92-72f42f527e96
-- title:
--   Theorem 16 — for $f\in S_\beta$: $\beta>\alpha^*[f]$ iff $\Phi(y)=\int_{[0,y)}\mu_\beta(du)/(y-u)^\varepsilon$ is non-decreasing for some $\varepsilon\in(0,\min\{\beta,1\})$
-- statement:
--   Let $\beta>0$ and let $f\in S_\beta$ be represented as
--   $$f(z)=\mu_\infty+\int_{[0,\infty)}\frac{\mu_\beta(du)}{(z+u)^\beta},\qquad z>0,$$
--   with $\mu_\infty\ge0$ and $\mu_\beta$ satisfying (2). Let $\alpha^*[f]=\inf\{\alpha>0: f\in S_\alpha\}$ be the exact Stieltjes order of $f$. Then
--   $$\beta>\alpha^*[f]\iff \exists\,\varepsilon\in(0,\min\{\beta,1\}):\ \ \Phi(y)=\int_{[0,y)}\frac{\mu_\beta(du)}{(y-u)^{\varepsilon}}\ \text{ is non-decreasing on }(0,\infty).$$
--
--   This is the paper's criterion of exactness: $\beta$ is the exact Stieltjes order of $f\in S_\beta$ precisely when, for every admissible $\varepsilon$, the fractional transform $\Phi$ of the representing measure fails to be monotone. Corollaries 1 and 2 of the paper (exactness from the growth of $\Phi$, and from compact support of $\mu_\beta$) follow from it.
--
--   **Formalization Note** Corrected reading: the paper prints the domain of integration in (25) as $(0,y)$; it is taken as $[0,y)$, the domain of (10), (11) and (29), which the proof uses. With $(0,y)$ the statement is false: $f(z)=z^{-\beta}$ has $\mu_\beta=\delta_0$, so the printed $\Phi$ is identically $0$ and hence non-decreasing, yet $z^{-\beta}\notin S_\alpha$ for $\alpha<\beta$. $\Phi$ is valued in $[0,\infty]$ and "non-decreasing" is monotonicity there. The representation is the published `StieltjesRepresentation` on $(0,\infty)$, with the atom $\mu_0$ of (1) inside $\mu_\beta$.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 11, Theorem 16, (24)–(25)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Theorem 16, p. 11: let `β > 0` and `f ∈ S_β` with representation `(a, μ_β)`. Then
`β > α*[f]` iff for some `ε ∈ (0, min{β, 1})` the function
`Φ(y) = ∫_{[0,y)} μ_β(du) / (y − u)^ε` is non-decreasing on `(0, ∞)`.
(Corrected reading: the paper prints the domain of (25) as `(0, y)`.) -/
theorem theorem_16 (β : ℝ) (hβ : 0 < β) (f : PositiveReal → ℝ) (a : ℝ) (μ : Measure ℝ≥0)
    (hf : StieltjesRepresentation β f a μ) :
    exactOrder f < β ↔
      ∃ ε : ℝ, 0 < ε ∧ ε < min β 1 ∧ MonotoneOn (Phi μ ε) (Set.Ioi 0) := by sorry

end GenStieltjes.ExactOrder
