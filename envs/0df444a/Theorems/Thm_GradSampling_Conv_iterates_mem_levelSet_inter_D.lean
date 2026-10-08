-- Prove2me | Theorems.Thm_GradSampling_Conv_iterates_mem_levelSet_inter_D
-- name    : GradSampling.Conv.iterates_mem_levelSet_inter_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:30.229968+00:00
-- url     : https://prove2.me/theorems/9ab39d1c-29ba-4b9a-9a1c-7c15defb7e00
-- title:
--   §2, p. 755 — every GS iterate lies in ℒ ∩ D, and f(x^{k+1}) ≤ f(x^k) − βt_k‖g^k‖
-- statement:
--   Let $x^0\in\mathcal L\cap D$, $\gamma,\beta\in(0,1)$, and consider any run of the GS algorithm (for any parameters $\epsilon_0,\nu_0,\mu,\theta$ and any sample realization $u^{kj}$) with stopping iteration $\tau$. Then
--
--   1. $x^k\in\mathcal L\cap D$ for every $k\le\tau$;
--   2. $f(x^{k+1})\le f(x^k)-\beta t_k\|g^k\|$ for every $k<\tau$;
--   3. the inequality in 2 is strict whenever $t_k>0$.
--
--   In particular the GS algorithm is a descent method that never leaves the compact set $\mathcal L$.
--
--   **Formalization Note** The decrease is stated with $\le$ because $t_k=0$ in the branch $\|g^k\|\le\nu_k$, where $x^{k+1}=x^k$; the strict inequality of Step 3 and of (2) is the third clause.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 755, §2, sentence after Step 4

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- §2, p. 755: every iterate of a run of the GS algorithm lies in `ℒ ∩ D`, and each iteration decreases
`f` by at least `β t_k ‖g^k‖`, strictly when `t_k > 0`. -/
theorem iterates_mem_levelSet_inter_D {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (xt x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ levelSet f xt ∩ D)
    (γ β ε0 ν0 μ θ : ℝ) (hγ : γ ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (u : ℕ → Fin m → EuclideanSpace ℝ (Fin n)) (X : ℕ → EuclideanSpace ℝ (Fin n)) (eps nu t : ℕ → ℝ)
    (g d : ℕ → EuclideanSpace ℝ (Fin n)) (τ : ℕ∞)
    (hrun : IsGSRun f D x0 γ β ε0 ν0 μ θ m u X eps nu t g d τ) :
    (∀ k : ℕ, (k : ℕ∞) ≤ τ → X k ∈ levelSet f xt ∩ D) ∧
      (∀ k : ℕ, (k : ℕ∞) < τ → f (X (k + 1)) ≤ f (X k) - β * t k * ‖g k‖) ∧
      (∀ k : ℕ, (k : ℕ∞) < τ → 0 < t k → f (X (k + 1)) < f (X k) - β * t k * ‖g k‖) := by sorry

end GradSampling.Conv
