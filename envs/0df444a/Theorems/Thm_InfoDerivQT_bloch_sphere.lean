-- Prove2me | Theorems.Thm_InfoDerivQT_bloch_sphere
-- name    : InfoDerivQT.bloch_sphere
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T16:01:35.283972+00:00
-- url     : https://prove2.me/theorems/8720a776-2a00-4fc5-858d-4f9338d7c5e3
-- title:
--   Theorem 13 — for $d_A=2$ the normalized states form the Bloch ball and $G_A\cong SO(3)$
-- statement:
--   Let $T$ satisfy the six principles and let $A$ be a system with a maximal set of two perfectly distinguishable pure states ($d_A=2$). Then there is an affine map $f:\mathrm{St}_{\mathbb R}(A)\to\mathbb R^3$, injective on $\mathrm{St}_1(A)$, such that
--
--   $$f\big(\mathrm{St}_1(A)\big)=\{x\in\mathbb R^3:\ x_1^2+x_2^2+x_3^2\le1\},$$
--
--   and the reversible transformations act on $f(\mathrm{St}_1(A))$ exactly as the rotation group:
--
--   1. for every reversible $\mathcal U$ of $A$ there is $R\in SO(3)$ with $f(\mathcal U\rho)=Rf(\rho)$ for all $\rho\in\mathrm{St}_1(A)$;
--   2. for every $R\in SO(3)$ there is a reversible $\mathcal U$ of $A$ with $f(\mathcal U\rho)=Rf(\rho)$ for all $\rho\in\mathrm{St}_1(A)$.
--
--   **Formalization Note** "Sphere" in the paper refers to the Bloch ball, whose boundary sphere is the set of pure states.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-22, Sec. X, Theorem 13 (The Bloch sphere)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem bloch_sphere (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    (φ : Fin 2 → Vec (T.size A)) (hφ : T.IsMaximalPerfDistPure A φ) :
    ∃ f : Vec (T.size A) →ᵃ[ℝ] (Fin 3 → ℝ),
      Set.InjOn f (T.St1 A) ∧ f '' T.St1 A = {x | ∑ i, x i ^ 2 ≤ 1} ∧
      (∀ U : Vec (T.size A) →ₗ[ℝ] Vec (T.size A), T.IsReversible A A U →
        ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
          ∀ ρ ∈ T.St1 A, f (U ρ) = Matrix.mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (f ρ)) ∧
      (∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
        ∃ U : Vec (T.size A) →ₗ[ℝ] Vec (T.size A), T.IsReversible A A U ∧
          ∀ ρ ∈ T.St1 A, f (U ρ) = Matrix.mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (f ρ)) := by sorry
end InfoDerivQT
