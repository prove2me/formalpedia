-- Prove2me | Theorems.Thm_HunterPDE_Semilinear_duhamel_lipschitz
-- name    : HunterPDE.Semilinear.duhamel_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:14:47.924313+00:00
-- url     : https://prove2.me/theorems/1c70c436-657c-4f84-88cf-515696088175
-- title:
--   Lemma 5.51 — the Duhamel map Φ maps C([0,T]; H^{2α}) to itself and is locally Lipschitz with factor CT^{1−α}
-- statement:
--   Let $n/4 < \alpha < 1$, $\lambda, \gamma \in \mathbb{R}$, $m \ge 1$, $g \in H^{2\alpha}(\mathbb{R}^n)$, and let $\Phi(u)(t) = e^{-tA}g + \int_0^t e^{-(t-s)A}F(u(s))\,ds$ with $F(h) = \lambda h - \gamma h^m$. Then
--   $$\Phi : C([0,T]; H^{2\alpha}(\mathbb{R}^n)) \to C([0,T]; H^{2\alpha}(\mathbb{R}^n)),$$
--   and for every $T_0 > 0$ there is a constant $C$, depending on $\alpha, m, n, \lambda, \gamma, T_0$ only, such that for all $0 < T \le T_0$ and all $u, v \in C([0,T]; H^{2\alpha})$,
--   $$\|\Phi(u) - \Phi(v)\|_{C([0,T];H^{2\alpha})} \le C\,T^{1-\alpha}\Big(1 + \|u\|^{m-1}_{C([0,T];H^{2\alpha})} + \|v\|^{m-1}_{C([0,T];H^{2\alpha})}\Big)\,\|u-v\|_{C([0,T];H^{2\alpha})}.$$
--
--   Together with the smoothing estimate, this makes $\Phi$ a contraction on a ball of $C([0,T];H^{2\alpha})$ for small $T$.
--
--   **Formalization Note.** The notes state the lemma under $\alpha > n/4$ with $C = C(\alpha,m,n)$. Their proof uses $\alpha < 1$ (the standing restriction of §5.5.3), bounds $F$'s Lipschitz constant by $|\lambda|$ and $|\gamma|$, and bounds $e^{t-s} \le e^T$; as printed (all $T > 0$, $\alpha \ge 1$ allowed, $C$ independent of $\lambda,\gamma,T$) the inequality fails for large $T$. The statement here adds $\alpha < 1$, $m \ge 1$, and lets $C$ depend on $\lambda, \gamma$ and an upper bound $T_0$ for $T$. $C$ is chosen before $g$, $T$, $u$, $v$. Norms are valued in $[0,\infty]$ (finite on $C([0,T];H^{2\alpha})$).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 155, Lemma 5.51

import Mathlib
import Definitions.Def_HunterPDE_Semilinear_SobolevHs
import Definitions.Def_HunterPDE_Semilinear_HeatSemigroup
import Definitions.Def_HunterPDE_Semilinear_MildSolution

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Semilinear

/-- Lemma 5.51 of Hunter, *Notes on PDEs* (p. 155): suppose `α > n/4` (and, as throughout
§5.5.3 and as the proof uses, `α < 1`). Let `Φ` be the map (5.40),
`Φ(u)(t) = e^{−tA} g + ∫₀ᵗ e^{−(t−s)A} F(u(s)) ds`, with `F(h) = λh − γh^m` (5.38), `A = −Δ`
(5.36) and `g ∈ H^{2α}(ℝⁿ)`. Then `Φ : C([0,T]; H^{2α}) → C([0,T]; H^{2α})` (5.41), and
`‖Φ(u) − Φ(v)‖_{C([0,T];H^{2α})}
   ≤ C T^{1−α} (1 + ‖u‖^{m−1}_{C([0,T];H^{2α})} + ‖v‖^{m−1}_{C([0,T];H^{2α})}) ‖u − v‖_{C([0,T];H^{2α})}`
for every `u, v ∈ C([0,T]; H^{2α})`.

Corrections to the page, read off its proof: the constant `C`, announced as `C(α, m, n)`,
also depends on the coefficients `λ, γ` (through the Lipschitz constant of `F`) and on an
upper bound `T₀` for `T` (through the factor `e^{t−s} ≤ e^{T}` from Lemma 5.50); `C` is chosen
before `g`, `T`, `u`, `v`. The nonlinearity has `m ≥ 1`. -/
theorem duhamel_lipschitz (n : ℕ) (α : ℝ) (hα : (n : ℝ) / 4 < α) (hα1 : α < 1)
    (lam gam : ℝ) (m : ℕ) (hm : 1 ≤ m) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C : ℝ, ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, hsNormReal n (2 * α) g < ⊤ →
      ∀ T : ℝ, 0 < T → T ≤ T₀ →
        (∀ u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ, IsContinuousHs n (2 * α) T u →
          IsContinuousHs n (2 * α) T (duhamelMap n lam gam m g u)) ∧
        (∀ u v : ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
          IsContinuousHs n (2 * α) T u → IsContinuousHs n (2 * α) T v →
          supHsNorm n (2 * α) T
              (fun t => duhamelMap n lam gam m g u t - duhamelMap n lam gam m g v t) ≤
            ENNReal.ofReal (C * T ^ (1 - α)) *
              (1 + supHsNorm n (2 * α) T u ^ (m - 1) + supHsNorm n (2 * α) T v ^ (m - 1)) *
              supHsNorm n (2 * α) T (fun t => u t - v t)) := by sorry

end HunterPDE.Semilinear
