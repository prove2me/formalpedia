-- Prove2me | Theorems.Thm_MassartDKW_Tight_lemma_3
-- name    : MassartDKW.Tight.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:40:23.371153+00:00
-- url     : https://prove2.me/theorems/78e774b3-97d1-4bac-b1ab-32b6cc8169a7
-- title:
--   Lemma 3, p. 1278 — midpoint lower bound for (1/2δ)∫_{s−δ}^{s+δ} g(u) exp(−λ²/2u(1 − u)) du, log g convex
-- statement:
--   Let $0<\delta<s<1-\delta$ and $s'=1-s$. Let $g$ be a positive function on $[s-\delta,s+\delta]$ such that $\log g$ is convex there. Then for every $\lambda>0$,
--   $$\frac1{2\delta}\int_{s-\delta}^{s+\delta}g(u)\exp\Bigl(-\frac{\lambda^2}{2u(1-u)}\Bigr)du\ \ge\ g(s)\exp\Bigl(-\frac{\lambda^2}{2ss'}\Bigr)\exp\Bigl(-\frac{\lambda^2\delta^2}6\Bigl(\bigl(s(s^2-\delta^2)\bigr)^{-1}+\bigl(s'(s'^2-\delta^2)\bigr)^{-1}\Bigr)\Bigr).$$
--
--   It converts the pointwise bound of Proposition 1 into a bound by an integral over a cell of width $1/n$, so that summing over $j$ produces the integrals $I_{a,b}(\lambda)$ of Lemma 4.
--
--   **Formalization Note** The page assumes $0<\delta\le s\le1-\delta$. At $\delta=s$ or $\delta=s'$ the printed lower bound contains $(s(s^2-\delta^2))^{-1}=\infty$ and is $0$, hence trivial; in Lean $0^{-1}=0$ would instead turn that boundary case into a different, stronger claim. The inequalities are therefore strict, $\delta<s<1-\delta$; no case with content is lost. In the application $\delta=1/(2n)<s$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1278, Lemma 3

import Mathlib

namespace MassartDKW.Tight

theorem lemma_3 (δ s : ℝ) (hδ : 0 < δ) (hδs : δ < s) (hs1 : s < 1 - δ) (g : ℝ → ℝ)
    (hg : ∀ u ∈ Set.Icc (s - δ) (s + δ), 0 < g u)
    (hlog : ConvexOn ℝ (Set.Icc (s - δ) (s + δ)) (fun u => Real.log (g u))) (l : ℝ) (hl : 0 < l) :
    g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s))) *
        Real.exp (-(l ^ 2 * δ ^ 2 / 6) *
          ((s * (s ^ 2 - δ ^ 2))⁻¹ + ((1 - s) * ((1 - s) ^ 2 - δ ^ 2))⁻¹)) ≤
      1 / (2 * δ) * ∫ u in (s - δ)..(s + δ), g u * Real.exp (-(l ^ 2) / (2 * u * (1 - u))) := by sorry

end MassartDKW.Tight
