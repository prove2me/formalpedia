-- Prove2me | Theorems.Thm_NatureSLT_IllPosed_tikhonov_convergence
-- name    : NatureSLT.IllPosed.tikhonov_convergence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:55.451996+00:00
-- url     : https://prove2.me/theorems/36f7871f-8fa2-418f-b158-8ca12d0eff22
-- title:
--   Theorem 7.1 — Tikhonov regularization converges to the exact solution in metric spaces
-- statement:
--   Let $E_1$ and $E_2$ be metric spaces and $A : E_1 \to E_2$ a continuous one-to-one map. Let $\Omega : E_1 \to [0, \infty]$ be a regularization functional: lower semicontinuous, with the set $\{g : \Omega(g) \le c\}$ compact for every $c > 0$. Suppose $f \in E_1$ with $\Omega(f) < \infty$ solves equation (7.12), $A f = F$. Instead of the exact right-hand side $F$, for every $\delta > 0$ an approximation $F_\delta \in E_2$ is given with
--
--   $$\rho_{E_2}(F, F_\delta) \le \delta .$$
--
--   Suppose the parameter $\gamma(\delta) > 0$ is chosen so that (7.17) holds:
--
--   $$\gamma(\delta) \to 0 \ \text{ for } \delta \to 0, \qquad \lim_{\delta \to 0} \frac{\delta^2}{\gamma(\delta)} \le r < \infty .$$
--
--   For each $\delta > 0$ let $f_\delta = f_\delta^{\gamma(\delta)}$ be any minimizer over $E_1$ of Tikhonov's functional
--
--   $$W_T(g) = \rho^2_{E_2}(A g, F_\delta) + \gamma(\delta)\, \Omega(g).$$
--
--   Then $f_\delta \to f$ in $E_1$ as $\delta \to 0^+$.
--
--   This is the basic convergence theorem for Tikhonov's regularization method (Tikhonov and Arsenin 1977): although the inverse of $A$ need not be continuous, so that solving $A g = F_\delta$ directly is unstable, the regularized solutions converge to the exact one as the data error vanishes, provided the regularization parameter decays no faster than $\delta^2$.
--
--   **Formalization Note** The limit in (7.17) need not exist; it is read as $\limsup_{\delta \to 0^+} \delta^2/\gamma(\delta) \le r$ with $r$ a finite nonnegative real, the limsup computed in $[0,\infty]$. $\delta \to 0$ is taken along $\delta > 0$, with $F_\delta$, $\gamma(\delta)$ and $f_\delta$ given for every $\delta > 0$. The book's tacit assumption that the exact solution lies in the domain $\{\Omega < \infty\}$ of $\Omega$ is explicit. The theorem covers every family of minimizers; their existence is not asserted. Properties 1–3 of $\Omega$ on p. 235 (imposed only for uniqueness) are not assumed.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 238, Theorem 7.1

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional

namespace NatureSLT.IllPosed

open Filter Topology
open scoped ENNReal NNReal

/-- Theorem 7.1 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §7.6.1, p. 238;
Tikhonov and Arsenin 1977). `A : E₁ → E₂` is a continuous one-to-one map between metric spaces
(the standing setting of (7.12), p. 233), `Ω` a regularization functional (p. 235), and `f` an
exact solution of `A f = F` lying in the domain `{Ω < ∞}` of `Ω`. For every `δ > 0` an
approximation `F_δ` with `ρ_{E₂}(F, F_δ) ≤ δ` is given, and `γ(δ) > 0` satisfies (7.17):
`γ(δ) → 0` as `δ → 0` and `lim_{δ→0} δ²/γ(δ) ≤ r < ∞` (read as `limsup`, computed in `[0, ∞]`).
Then any choice of minimizers `f_δ` of `W_T(g) = ρ²_{E₂}(A g, F_δ) + γ(δ) Ω(g)` on `E₁`
converges to `f` as `δ → 0⁺`. -/
theorem tikhonov_convergence {E₁ E₂ : Type*} [MetricSpace E₁] [MetricSpace E₂]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤)
    (Fδ : ℝ → E₂) (hFδ : ∀ δ : ℝ, 0 < δ → dist F (Fδ δ) ≤ δ)
    (γ : ℝ → ℝ) (hγpos : ∀ δ : ℝ, 0 < δ → 0 < γ δ)
    (hγ : Tendsto γ (𝓝[>] 0) (𝓝 0))
    (r : ℝ≥0) (hr : limsup (fun δ : ℝ => ENNReal.ofReal (δ ^ 2 / γ δ)) (𝓝[>] 0) ≤ (r : ℝ≥0∞))
    (fδ : ℝ → E₁)
    (hmin : ∀ δ : ℝ, 0 < δ → ∀ g : E₁,
      tikhonovFunctional A Ω (γ δ) (Fδ δ) (fδ δ) ≤ tikhonovFunctional A Ω (γ δ) (Fδ δ) g) :
    Tendsto fδ (𝓝[>] 0) (𝓝 f) := by sorry

end NatureSLT.IllPosed
