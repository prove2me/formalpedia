-- Prove2me | Theorems.Thm_Katyusha_SC_theorem_2_1
-- name    : Katyusha.SC.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:36.204582+00:00
-- url     : https://prove2.me/theorems/6ca9c9ba-2823-4924-a9cc-550227d3473a
-- title:
--   Theorem 2.1 — accelerated linear convergence of Katyusha
-- statement:
--   Consider $F(x)=n^{-1}\sum_{i=1}^n f_i(x)+\psi(x)$ on $\mathbb R^d$, where $n\ge1$, each $f_i$ is convex and $L$ smooth with its actual gradient, $\psi$ is $\sigma$ strongly convex, and $L,\sigma>0$. Run Algorithm 1, Option I, from $x_0$ for $S\ge0$ epochs with its prescribed length $m=2n$ and parameters $\tau_2=1/2$, $\tau_1=\min\{\sqrt{m\sigma}/\sqrt{3L},1/2\}$ and $\alpha=1/(3\tau_1L)$. Let $x^*$ minimize the full objective $F$, and let $\widetilde x^S$ be the returned weighted snapshot. The expectation is over all independent uniform indices drawn during the run. Then
--   $$\begin{cases}\mathbb E F(\widetilde x^S)-F(x^*)\le4(1+\sqrt{\sigma/(3Lm)})^{-Sm}(F(x_0)-F(x^*)),&m\sigma/L\le3/4,\\\mathbb E F(\widetilde x^S)-F(x^*)\le3(2/3)^S(F(x_0)-F(x^*)),&m\sigma/L>3/4.\end{cases}$$
--   This is the paper's accelerated linear objective-error rate for strongly convex finite sums.
--
--   **Formalization Note** The paper writes both rates with $O(\cdot)$; its proof yields the explicit factors 4 and 3 used here. The paper's subsequent iteration-complexity paraphrase is outside this theorem. The proximal map is required to minimize the actual regularizer's proximal objective at every positive step size. The regularizer is real valued and may be nondifferentiable.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 7, Theorem 2.1; explicit constants derived from §2.2, pp. 12–13

import Definitions.Def_Katyusha_SC_run

namespace Katyusha.SC

/-- Theorem 2.1, p. 7: both accelerated regimes for Algorithm 1, Option I. -/
theorem theorem_2_1 {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (hp : IsValid p) (hP : IsProxMap p.ψ P) (x0 xstar : Vec d)
    (hmin : ∀ x, objective p xstar ≤ objective p x) (S : ℕ) :
    let m := 2 * n
    ((m : ℝ) * p.modulus / p.smoothness ≤ 3 / 4 →
      expectedObjective p P m S x0 - objective p xstar ≤
        4 * gap p xstar x0 /
          (1 + Real.sqrt (p.modulus / (3 * p.smoothness * (m : ℝ)))) ^ (S * m)) ∧
    (3 / 4 < (m : ℝ) * p.modulus / p.smoothness →
      expectedObjective p P m S x0 - objective p xstar ≤
        3 * ((2 / 3 : ℝ) ^ S) * gap p xstar x0) := by sorry

end Katyusha.SC
