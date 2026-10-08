-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_tail_j1
-- name    : NetTraffic.PoissonStable.tail_j1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:13.484975+00:00
-- url     : https://prove2.me/theorems/0972ebc2-fb47-4f1d-b263-7a219e1f8594
-- title:
--   §4.4, pp. 37–38 — λT P(j₁ > b(λT)x) → x^{−α} for every x > 0
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Let $m_1=(\mathbb L\times F_{\mathrm{on}})(R_1)$ with $R_1=\{(s,y):0<s\le T,\ y>0,\ s+y\le T\}$ and let $j_1$ have the law (4.4): the second marginal of $\mathbb L(ds)F_{\mathrm{on}}(dy)/m_1$ restricted to $R_1$.
--
--   If Condition 1 holds, then for every $x>0$
--   $$\lambda T\,P\big(j_1>b(\lambda T)\,x\big)\longrightarrow x^{-\alpha}\qquad(T\to\infty).$$
--
--   This tail limit identifies the Lévy measure $\alpha x^{-\alpha-1}dx$ on $(0,\infty)$ of the limiting totally skewed stable law.
--
--   **Formalization Note** The statement is deterministic: it concerns $F_{\mathrm{on}}$, $\lambda$ and the law (4.4) only.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), pp. 37–38, §4.4, display "λT P(j₁ > b(λT)x) … ∼ x^{−α}"

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem tail_j1
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam) :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun T => lam T * T * (j1Law Fon T).real (Set.Ioi (b Fon (lam T * T) * x)))
        atTop (𝓝 (x ^ (-α))) := by sorry

end NetTraffic.PoissonStable
