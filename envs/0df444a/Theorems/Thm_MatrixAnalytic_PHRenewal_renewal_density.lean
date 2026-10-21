-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_renewal_density
-- name    : MatrixAnalytic.PHRenewal.renewal_density
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:34.446804+00:00
-- url     : https://prove2.me/theorems/98373eac-0de8-48f1-a7e4-6972f23b0901
-- title:
--   Theorem 3.1.2 — the renewal density of the (possibly delayed) PH renewal process is $r(x) = \boldsymbol\beta\exp(Dx)\boldsymbol t$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be an irreducible PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and $\boldsymbol\tau\mathbf 1=1$, and let $D=T+\boldsymbol t\cdot\boldsymbol\tau$. Consider the (possibly delayed) PH renewal process whose initial phase has distribution $\boldsymbol\beta$ ($\boldsymbol\beta\ge\mathbf 0$, $\boldsymbol\beta\mathbf 1=1$), and let $N(x)$ be the number of renewals in $(0,x]$. Its renewal density, the derivative $r(x)$ of the renewal function $x\mapsto\mathrm E_{\boldsymbol\beta}[N(x)]=\sum_{k\ge0}k\,\boldsymbol\beta P(k,x)\mathbf 1$, exists for every $x>0$ and equals
--   $$r(x) = \boldsymbol\beta\exp(Dx)\boldsymbol t, \qquad x>0.$$
--
--   Setting $\boldsymbol\beta=\boldsymbol\tau$ gives the renewal density of the nondelayed process, from which the renewal function of Theorem 3.1.4 is obtained.
--
--   **Formalization Note** The book defines the renewal density by $r(x)=R'(x)$ (p. 62); the statement asserts that $x\mapsto \mathrm E_{\boldsymbol\beta}[N(x)]$ has derivative $\boldsymbol\beta\exp(Dx)\boldsymbol t$ at each $x>0$ (`HasDerivAt`). Adding the constant renewal at time $0$ does not change the derivative. The expectation is the series of the definition `Counting`; a statement about its derivative implies its convergence near $x$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 63, Theorem 3.1.2

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem renewal_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T)
    (β : ι → ℝ) (hβ_nonneg : ∀ i, 0 ≤ β i) (hβ_sum : ∑ i, β i = 1)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => meanCount β τ T y)
      (β ⬝ᵥ (NormedSpace.exp (x • phaseGen τ T) *ᵥ exitVec T)) x := by sorry

end MatrixAnalytic.PHRenewal
