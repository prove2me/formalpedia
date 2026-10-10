-- Prove2me | Theorems.Thm_OnsagerReciprocal_onsager_reciprocal_relations
-- name    : OnsagerReciprocal.onsager_reciprocal_relations
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:02:47.483437+00:00
-- url     : https://prove2.me/theorems/74b42420-96f0-47e5-bbaf-099798fe41e2
-- title:
--   Onsager's principle: symmetry of kinetic coefficients $\gamma_{ik}=\gamma_{ki}$
-- statement:
--   **Onsager's principle (principle of symmetry of kinetic coefficients).**
--
--   Let $x=(x_1,\dots,x_n)$ be fluctuations of $n$ thermodynamic quantities from equilibrium, distributed according to the Gaussian law
--   $$w(x)=\tilde A\,e^{-\frac12\beta_{ik}x_ix_k},$$
--   where $\beta$ is a positive definite symmetric real matrix (in the source, $\beta_{ik}=-\frac1k\partial^2S/\partial x_i\partial x_k$). In the quasi-stationary regime $\dot x_i=-\lambda_{ik}x_k$ for a real matrix $\lambda$, so the mean value at time $t$ of the fluctuation that equals $x$ at $t=0$ is $\xi(t)=e^{-t\lambda}x$. The thermodynamic conjugate quantities are $X_i=\beta_{ik}x_k$, and the kinetic coefficients are
--   $$\gamma_{ik}=\lambda_{il}\,(\beta^{-1})_{lk},\qquad\text{so that}\qquad \dot x_i=-\gamma_{ik}X_k .$$
--   Assume the **symmetry of fluctuations under time reversal**: for every $t\ge0$ and all $i,k$,
--   $$\langle x_i(t)\,x_k(0)\rangle=\langle x_i(0)\,x_k(t)\rangle,\qquad\text{i.e.}\qquad \langle\xi_i(t)\,x_k\rangle=\langle x_i\,\xi_k(t)\rangle,$$
--   where $\langle\cdot\rangle$ is the average with respect to $w$. Then the matrix of kinetic coefficients is symmetric:
--   $$\gamma_{ik}=\gamma_{ki}\qquad\text{for all }i,k .$$
--
--   This is the abstract form of the Onsager reciprocal relations, which express the equality of cross-coefficients between thermodynamic flows and forces (e.g. Peltier/Seebeck, thermodiffusion/Dufour) near equilibrium.
--
--   **Formalization Note** The Gaussian average is the ratio $\int f\,w\,dx/\int w\,dx$ over Lebesgue measure on $\mathbb R^n$ (so the normalizing constant $\tilde A$ cancels). The time-reversal hypothesis is imposed only for $t\ge0$, where the quasi-stationary relaxation $\xi(t)=e^{-t\lambda}x$ is meant to apply.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem onsager_reciprocal_relations {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      timeCorrelation β lam t i k = timeCorrelation β lam t k i) :
    ∀ i k : Fin n, kineticCoeff β lam i k = kineticCoeff β lam k i := by sorry
end OnsagerReciprocal
