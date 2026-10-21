-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_proposition_D_3
-- name    : LiqProvision.Oligopoly.proposition_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:49.751487+00:00
-- url     : https://prove2.me/theorems/35a3b362-b112-4707-9a69-4232a811ceb9
-- title:
--   Proposition D.3, p. 34 — refined Efron theorem: E[U | U + V = w] is C¹ with positive derivative
-- statement:
--   Let $U$ and $V$ be independent real random variables with positive log-concave densities $f_U$ and $f_V$, and let $W=U+V$. The conditional mean
--   $$g(w)=E[U\mid W=w]=\frac{\int_{\mathbb R}(w-v)\,f_U(w-v)\,f_V(v)\,dv}{\int_{\mathbb R}f_U(w-v)\,f_V(v)\,dv}$$
--   is continuously differentiable and satisfies $g'(w)>0$ for every $w\in\mathbb R$.
--
--   This is a refinement of Efron's theorem (strict monotonicity of the conditional mean), and it is the tool behind Proposition 3.1.
--
--   **Formalization Note.** Generic statement: it uses no model objects. Densities are real functions; a probability density is positive, integrable, of total integral $1$, and log-concave means that $\log f$ is concave on $\mathbb R$. The conditional mean is written as the ratio displayed above, which is the formula for $E[U\mid W=w]$ used in the proof on p. 34; no random variables appear in the Lean statement.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 34, Proposition D.3

import Mathlib

namespace LiqProvision.Oligopoly
theorem proposition_D_3 (fU fV : ℝ → ℝ)
    (hUpos : ∀ x, 0 < fU x) (hUint : MeasureTheory.Integrable fU) (hUmass : ∫ x, fU x = 1)
    (hUlc : ConcaveOn ℝ Set.univ (fun x => Real.log (fU x)))
    (hVpos : ∀ x, 0 < fV x) (hVint : MeasureTheory.Integrable fV) (hVmass : ∫ x, fV x = 1)
    (hVlc : ConcaveOn ℝ Set.univ (fun x => Real.log (fV x))) :
    ContDiff ℝ 1 (fun w => (∫ v, (w - v) * fU (w - v) * fV v) / ∫ v, fU (w - v) * fV v) ∧
      ∀ w, 0 < deriv (fun w =>
        (∫ v, (w - v) * fU (w - v) * fV v) / ∫ v, fU (w - v) * fV v) w := by sorry
end LiqProvision.Oligopoly
