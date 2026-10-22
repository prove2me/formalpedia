-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_renewal_function
-- name    : MatrixAnalytic.PHRenewal.renewal_function
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:25.927291+00:00
-- url     : https://prove2.me/theorems/ad44477d-8198-4a25-b70d-42e6c17b0b75
-- title:
--   Theorem 3.1.4 — $R(x) = 1 + xM^{-1} + \boldsymbol\tau(\exp(Dx) - I)(D-\Pi)^{-1}\boldsymbol t$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be an irreducible PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and no atom at $0$ ($\boldsymbol\tau\mathbf 1=1$). Let $D=T+\boldsymbol t\cdot\boldsymbol\tau$ be the generator of the phase process, $\boldsymbol\pi=(\boldsymbol\tau T^{-1}\mathbf 1)^{-1}\boldsymbol\tau T^{-1}$ its stationary vector, $\Pi=\mathbf 1\cdot\boldsymbol\pi$, and
--   $$M=\boldsymbol\tau(-T)^{-1}\mathbf 1$$
--   the mean interrenewal time. Let $R(x)$ be the renewal function of the PH renewal process starting with a renewal at time $0$: the expected number of renewals in $[0,x]$, that is $R(x)=1+\sum_{k\ge0}k\,\boldsymbol\tau P(k,x)\mathbf 1$ with $P_{ij}(k,x)=\mathrm P[N(x)=k,\ J(x)=j\mid N(0)=0,\ J(0)=i]$. Then for every $x\ge0$ the matrix $D-\Pi$ is nonsingular, the series defining $R(x)$ converges, and
--   $$R(x) = 1 + xM^{-1} + \boldsymbol\tau\bigl(\exp(Dx) - I\bigr)(D-\Pi)^{-1}\boldsymbol t.$$
--
--   The formula separates the linear growth $x/M$ of the renewal function (the elementary renewal theorem) from a correction term that converges as $x\to\infty$, and gives $R(x)$ in closed form from the representation alone.
--
--   **Formalization Note** $R(x)$ is defined as an expectation of the number of renewals, through the transition function of the process $(N(x),J(x))$ restricted to finitely many levels (definition `Counting`), not as $1+\int_0^x r(u)\,du$; the identity is therefore not definitional. Nonsingularity of $D-\Pi$ and convergence of the series are part of the conclusion, so neither the matrix inverse nor the `tsum` can take a junk value. $\exp$ is Mathlib's `NormedSpace.exp` on real matrices.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 64, Theorem 3.1.4

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem renewal_function {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T)
    (x : ℝ) (hx : 0 ≤ x) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    Summable (fun k : ℕ => (k : ℝ) * (τ ⬝ᵥ (countProb τ T k x *ᵥ fun _ => 1))) ∧
    renewalFunction τ T x =
      1 + x * (meanInterrenewal τ T)⁻¹ +
        τ ⬝ᵥ (((NormedSpace.exp (x • phaseGen τ T) - 1) *
          (phaseGen τ T - statMatrix τ T)⁻¹) *ᵥ exitVec T) := by sorry

end MatrixAnalytic.PHRenewal
