-- Prove2me | Theorems.Thm_LariviereIGFR_Char_theorem_1
-- name    : LariviereIGFR.Char.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:09.430237+00:00
-- url     : https://prove2.me/theorems/238a2f06-0a73-4e1c-801e-2911dfdc860b
-- title:
--   Theorem 1, p. 603 — X IGFR ⇔ log X IFR ⇔ X ⪯hr λX (λ ≥ 1) ⇔ Φ̄(ξ/θ) TP₂
-- statement:
--   Let $X$ be a nonnegative random variable with distribution function $\Phi$, survival function $\bar\Phi = 1 - \Phi$ and density $\varphi$, taken as the version that is the derivative of $\Phi$ on the support $(\alpha,\beta)$ and $0$ to its left. Write $h = \varphi/\bar\Phi$ for its failure rate and $g(\xi) = \xi h(\xi)$ for its generalized failure rate. Let $X_L = \log X$, with density $\varphi_L(\xi) = e^\xi\varphi(e^\xi)$, and for $\lambda \ge 1$ let $\lambda X$ have density $\varphi(\xi/\lambda)/\lambda$. The following statements are equivalent:
--
--   1. $X$ is IGFR: $g$ is weakly increasing on $\{\xi : \Phi(\xi) < 1\}$.
--   2. $X_L$ is IFR: its failure rate $h_L$ is weakly increasing on $\{\xi : \Phi_L(\xi) < 1\}$.
--   3. $X \preceq_{hr} \lambda X$ for every $\lambda \ge 1$: $h(\xi) \ge h_\lambda(\xi)$ for all $\xi \ge 0$ with $\Phi(\xi) < 1$.
--   4. $f(\xi,\theta) = \bar\Phi(\xi/\theta)$ is TP₂ on $(0,\infty)^2$:
--   $$\bar\Phi(\xi_1/\theta_1)\,\bar\Phi(\xi_2/\theta_2) - \bar\Phi(\xi_1/\theta_2)\,\bar\Phi(\xi_2/\theta_1) \ge 0 \quad\text{for } 0<\xi_1<\xi_2,\ 0<\theta_1<\theta_2.$$
--
--   The IGFR condition makes the revenue and newsvendor-contract problems of operations management unimodal, but it is hard to check directly. Theorem 1 replaces it by an IFR condition on $\log X$, by a hazard-rate comparison under scaling, or by a total-positivity condition, each of which brings the known theory of IFR distributions to bear.
--
--   **Formalization Note** $X$ is represented by its law $\mu$ on $\mathbb R$ with $\mu((-\infty,0)) = 0$; $X_L$ and $\lambda X$ are the image laws under the measurable maps $\log$ and $x \mapsto \lambda x$. The density is pinned to its regular version, because IFR and IGFR read it pointwise and the theorem is false for an arbitrary version. The rates are read on $\{\Phi < 1\}$ (where $\bar\Phi > 0$), and the hazard-rate order on $\xi \ge 0$ with $\Phi(\xi) < 1$, where the paper's $h$ is finite. Part 4 is stated on $(0,\infty)^2$: $\theta > 0$ is forced by $\xi/\theta$, and $\xi \le 0$ adds nothing since $\bar\Phi(\xi/\theta) = 1$ there.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, Theorem 1

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem theorem_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    List.TFAE
      [ IsIGFR μ φ,
        IsIFR (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)),
        ∀ c : ℝ, 1 ≤ c → HazardRateLE μ φ (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c),
        IsTP2On (fun ξ θ => survival μ (ξ / θ)) (Set.Ioi 0) (Set.Ioi 0) ] := by sorry

end LariviereIGFR.Char
