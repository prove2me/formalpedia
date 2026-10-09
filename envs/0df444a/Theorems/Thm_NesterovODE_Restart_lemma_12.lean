-- Prove2me | Theorems.Thm_NesterovODE_Restart_lemma_12
-- name    : NesterovODE.Restart.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:48.14214+00:00
-- url     : https://prove2.me/theorems/4f253569-0a86-4220-87ee-1850783f6988
-- title:
--   Lemma 12, p. 23 — a universal C > 0 with f(X(T)) − f⋆ ≤ (1 − Cµ/L)(f(x₀) − f⋆)
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $0<\mu\le L$, let $f\in\mathcal S_{\mu,L}$ on $\mathbb R^n$ with minimizer $x^\star$ and $f^\star=f(x^\star)$, let $x_0\ne x^\star$, let $X$ solve (3) from $x_0$, and let $T$ be its speed restarting time. Then
--
--   $$f(X(T))-f^\star\le\Bigl(1-\frac{C\mu}L\Bigr)\bigl(f(x_0)-f^\star\bigr).$$
--
--   Each speed restart therefore reduces the optimality gap by a constant factor depending only on the condition number $L/\mu$. Together with Lemma 13 it gives the linear rate of Theorem 10.
--
--   **Formalization Note** $C$ is chosen before the dimension $n$, $f$, $\mu$, $L$, $x_0$ and the trajectory, which is what "universal" means. $T$ is `restartTime`, the `sSup` of the set in the definition; by Lemmas 25 and 13 that set is nonempty and bounded, so $T$ is the paper's value. The hypothesis $x_0\ne x^\star$ is the convention of §5 (p. 22).
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 23, Lemma 12 (proof pp. 23–24)

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Lemma 12 (p. 23): there is a universal constant `C > 0` (chosen before the dimension,
`f`, `μ`, `L`, `x₀`) such that `f(X(T)) − f⋆ ≤ (1 − Cμ/L)(f(x₀) − f⋆)`, where `T` is the
speed restarting time of the solution of (3) from `x₀`. Convention of §5: `x₀ ≠ x⋆`. -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) → x₀ ≠ xstar →
        ∀ (X V : ℝ → NesterovODE.WellPosed.E n), NesterovODE.StrongCvx.IsSolution f 3 x₀ X V →
          f (X (restartTime f X V)) - f xstar ≤ (1 - C * μ / L) * (f x₀ - f xstar) := by sorry

end NesterovODE.Restart
