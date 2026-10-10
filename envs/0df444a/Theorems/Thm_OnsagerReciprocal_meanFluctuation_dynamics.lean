-- Prove2me | Theorems.Thm_OnsagerReciprocal_meanFluctuation_dynamics
-- name    : OnsagerReciprocal.meanFluctuation_dynamics
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:59:18.248106+00:00
-- url     : https://prove2.me/theorems/eabd7283-49d8-47b2-a1c1-6464b9653a5d
-- title:
--   Mean values relax as $\dot\xi=-\gamma\,\Xi$
-- statement:
--   Let $\beta$ be a positive definite real symmetric $n\times n$ matrix, $\lambda$ a real $n\times n$ matrix, $\gamma=\lambda\beta^{-1}$, and $x_0\in\mathbb R^n$. Let $\xi(t)=e^{-t\lambda}x_0$ be the mean value at time $t$ of the fluctuation that equals $x_0$ at $t=0$, and $\Xi(t)=\beta\,\xi(t)$. Then
--   $$\xi(0)=x_0\qquad\text{and}\qquad \dot\xi_i(t)=-\gamma_{ik}\,\Xi_k(t)\quad\text{for all }t\in\mathbb R .$$
--   This expresses the relaxation of mean values in terms of the kinetic coefficients and the conjugate mean values.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem meanFluctuation_dynamics {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x₀ : Fin n → ℝ) :
    meanFluctuation lam 0 x₀ = x₀ ∧
      ∀ t : ℝ, HasDerivAt (fun s => meanFluctuation lam s x₀)
        (-(kineticCoeff β lam *ᵥ meanConjugate β lam t x₀)) t := by sorry
end OnsagerReciprocal
