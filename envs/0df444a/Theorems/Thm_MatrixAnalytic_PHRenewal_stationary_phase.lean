-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_stationary_phase
-- name    : MatrixAnalytic.PHRenewal.stationary_phase
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:34.809728+00:00
-- url     : https://prove2.me/theorems/6b2860a3-3bb1-4e28-b87e-7758c5447bca
-- title:
--   Lemma 3.1.3 — $D - \Pi$ is nonsingular, $\boldsymbol\pi$ is the stationary vector of $D$ and $\boldsymbol\pi(D-\Pi)^{-1} = -\boldsymbol\pi$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be an irreducible PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and $\boldsymbol\tau\mathbf 1 = 1$. Let $D = T+\boldsymbol t\cdot\boldsymbol\tau$ be the generator of the phase process, and set
--   $$\boldsymbol\pi = (\boldsymbol\tau T^{-1}\mathbf 1)^{-1}\boldsymbol\tau T^{-1}, \qquad \Pi = \mathbf 1\cdot\boldsymbol\pi. \tag{3.1}$$
--   Then:
--
--   1. the matrix $D-\Pi$ is nonsingular;
--   2. $\boldsymbol\pi$ is the stationary probability vector of the phase process: $\boldsymbol\pi\ge\mathbf 0$, $\boldsymbol\pi D=\mathbf 0$, $\boldsymbol\pi\mathbf 1=1$, and it is the only solution of the system $\boldsymbol x D=\mathbf 0$, $\boldsymbol x\mathbf 1=1$;
--   3. $$\boldsymbol\pi(D-\Pi)^{-1} = -\boldsymbol\pi.$$
--
--   The matrix $(D-\Pi)^{-1}$ is the deviation matrix that appears in the closed form of the renewal function (Theorem 3.1.4).
--
--   **Formalization Note** Nonsingularity is part of the conclusion (`IsUnit (D - Π)`), so the inverse in clause 3 is a true inverse. Clause 2 spells out "the stationary probability vector, i.e., the solution of the system πD = 0, π1 = 1": nonnegativity, the two equations, and uniqueness among all real row vectors.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 64, Lemma 3.1.3, Eq. (3.1)

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem stationary_phase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    (∀ i, 0 ≤ statVec τ T i) ∧
    statVec τ T ᵥ* phaseGen τ T = 0 ∧
    ∑ i, statVec τ T i = 1 ∧
    (∀ v : ι → ℝ, v ᵥ* phaseGen τ T = 0 → ∑ i, v i = 1 → v = statVec τ T) ∧
    statVec τ T ᵥ* (phaseGen τ T - statMatrix τ T)⁻¹ = -statVec τ T := by sorry

end MatrixAnalytic.PHRenewal
