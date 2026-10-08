-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_eq_4_11_4_12
-- name    : MifflinSemismooth.Composition.eq_4_11_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:23.566975+00:00
-- url     : https://prove2.me/theorems/529b0c6e-9a32-44ee-9642-6a9770b0da1c
-- title:
--   Equations (4.11)–(4.12) — first-order expansion of the component map
-- statement:
--   Suppose each component $f_i$ is Lipschitz on bounded sets and has one-sided directional derivative $L_i=f_i'(x;d)$. Let $z=(L_1,\ldots,L_m)$, $t_k>0$ tend to zero, and $\theta_k/t_k\to0$. Then the remainder in $Y(x+t_kd+\theta_k)=Y(x)+t_kz+\phi_k$ satisfies
--
--   $$\frac{\phi_k}{t_k}\longrightarrow0\quad\text{in }\mathbb R^m. $$
--
--   This is the first-order component expansion used in the proof of Theorem 5.
--
--   **Formalization Note** The page derives this claim from component Lipschitzness and existence of the directional derivatives; stating those hypotheses instead of semismoothness isolates the displayed argument.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), pp. 15–16, proof of Theorem 5, (4.11)–(4.12)

import Mathlib
import Definitions.Def_MifflinSemismooth_Composition_Setting
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded

open Filter Topology

namespace MifflinSemismooth.Composition

theorem eq_4_11_4_12 {n m : ℕ}
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ClarkeGradients.Shared.LipschitzOnBounded (f i))
    (x d : EuclideanSpace ℝ (Fin n)) (L : Fin m → ℝ)
    (hL : ∀ i, MifflinSemismooth.Extremal.HasDirDeriv (f i) x d (L i))
    (t : ℕ → ℝ) (θ : ℕ → EuclideanSpace ℝ (Fin n))
    (htpos : ∀ k, 0 < t k) (htlim : Tendsto t atTop (𝓝 0))
    (hθ : Tendsto (fun k => (t k)⁻¹ • θ k) atTop (𝓝 0)) :
    let z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 L
    Tendsto (fun k => (t k)⁻¹ •
      (Y f (x + t k • d + θ k) - Y f x - t k • z)) atTop (𝓝 0) := by sorry

end MifflinSemismooth.Composition
