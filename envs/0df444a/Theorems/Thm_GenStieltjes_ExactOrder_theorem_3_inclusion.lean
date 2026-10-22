-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_theorem_3_inclusion
-- name    : GenStieltjes.ExactOrder.theorem_3_inclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:09.875041+00:00
-- url     : https://prove2.me/theorems/ba962883-1f16-4085-803a-444c6dc17ffb
-- title:
--   Theorem 3, first part — $S_\alpha\subset S_\beta$ for $\alpha<\beta$, with the representing measure $\mu_\beta$ of (10)
-- statement:
--   Let $0<\alpha<\beta$ and let $f\in S_\alpha$ be represented as
--   $$f(z)=\mu_\infty+\int_{[0,\infty)}\frac{\mu_\alpha(du)}{(z+u)^\alpha},\qquad z>0,$$
--   with $\mu_\infty\ge 0$ and $\mu_\alpha$ satisfying (2). Let $\mu_\beta$ be the measure on $[0,\infty)$ given by (10),
--   $$\mu_\beta(dy)=\frac{\Gamma(\beta)\,dy}{\Gamma(\alpha)\Gamma(\beta-\alpha)}\int_{[0,y)}\frac{\mu_\alpha(du)}{(y-u)^{\alpha+1-\beta}} .$$
--   Then:
--   1. $\mu_\beta\in\mathcal M_\beta$ and $f(z)=\displaystyle\int_{(0,\infty)}\frac{\mu_\beta(dy)}{(y+z)^\beta}+\mu_\infty$ for every $z>0$, which is (9); that is, $(\mu_\infty,\mu_\beta)$ is a representation of $f$ in $S_\beta$;
--   2. $\mu_\beta(\{0\})=0$, so the integral in (9) is over $(0,\infty)$;
--   3. consequently $S_\alpha\subset S_\beta$.
--
--   The theorem shows that the classes $S_\alpha$ increase with $\alpha$ and identifies the passage $\mu_\alpha\mapsto\mu_\beta$ as a Riemann–Liouville fractional integral of order $\beta-\alpha$ (Remark 2). It is one direction of the proof of Theorem 16.
--
--   **Formalization Note** The class $S_\alpha$ and the representation are the published definitions `StieltjesClass` and `StieltjesRepresentation` (functions on $(0,\infty)$, representing measure on `ℝ≥0` carrying the atom $\mu_0$ at $0$, constant $\mu_\infty\ge0$). The constant $\mu_\infty$ is the same in both representations.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 4, Theorem 3, (9)–(10)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Theorem 3, first part, (9)–(10), p. 4: if `0 < α < β` and `f ∈ S_α` is represented by
`(a, μ_α)`, then `f` is represented in `S_β` by `(a, μ_β)` with `μ_β` the measure (10),
which has no atom at `0`; in particular `S_α ⊆ S_β`. -/
theorem theorem_3_inclusion (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (f : PositiveReal → ℝ) (a : ℝ) (μ : Measure ℝ≥0)
    (hf : StieltjesRepresentation α f a μ) :
    StieltjesRepresentation β f a (thm3Measure α β μ) ∧
      thm3Measure α β μ {0} = 0 ∧
      StieltjesClass α ⊆ StieltjesClass β := by sorry

end GenStieltjes.ExactOrder
