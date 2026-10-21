-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_count_ode
-- name    : MatrixAnalytic.PHRenewal.count_ode
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:28.9305+00:00
-- url     : https://prove2.me/theorems/df63cdba-b8b9-4218-8cbd-6dc0cd449e00
-- title:
--   Theorem 3.2.1 — the differential equations (3.2)–(3.3) for $P(k,x)$ and $P^*(z,x) = \exp\{(T + z\boldsymbol t\cdot\boldsymbol\tau)x\}$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be an irreducible PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and $\boldsymbol\tau\mathbf 1=1$. For the PH renewal process let $N(x)$ be the number of renewals in $(0,x]$, $J(x)$ the phase at time $x$, and
--   $$P_{ij}(k,x) = \mathrm P[N(x)=k,\ J(x)=j\mid N(0)=0,\ J(0)=i], \qquad P^*(z,x)=\sum_{k\ge0}z^kP(k,x).$$
--   Then for $x\ge 0$ (derivatives at $x=0$ taken from the right)
--   $$P'(0,x) = TP(0,x), \tag{3.2}$$
--   $$P'(k,x) = TP(k,x) + \boldsymbol t\cdot\boldsymbol\tau P(k-1,x)\qquad\text{for } k\ge1, \tag{3.3}$$
--   with $P(0,0)=I$ and $P(k,0)=0$ for $k\ge 1$; and for every real $z$ with $|z|\le1$ and every $x\ge0$ the series $P^*(z,x)$ converges and
--   $$P^*(z,x) = \exp\{(T+z\,\boldsymbol t\cdot\boldsymbol\tau)x\}. \tag{3.4}$$
--
--   These are the matrix analogues of the Kolmogorov equations and the probability generating function of the Poisson process ($n=1$, $T=-\lambda$, $\tau=1$).
--
--   **Formalization Note** $P(k,x)$ is the entry block of $\exp(Q_kx)$ for the generator $Q_k$ of $(N(x),J(x))$ restricted to levels $0,\dots,k$ (see the definition `Counting`). Derivatives are `HasDerivWithinAt` on $[0,\infty)$, the matrices carrying the entrywise topology. The book leaves the range of $z$ implicit; the statement takes real $z$ with $|z|\le1$, where $P^*(z,x)$ is a generating function of a probability distribution, and asserts convergence through `HasSum`. Equation (3.3) is written with $k+1$ in place of $k\ge1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 65, Theorem 3.2.1, Eqs. (3.2)–(3.4)

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem count_ode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    (∀ x : ℝ, 0 ≤ x →
      HasDerivWithinAt (fun y => countProb τ T 0 y)
        (T * countProb τ T 0 x) (Set.Ici 0) x) ∧
    (∀ k : ℕ, ∀ x : ℝ, 0 ≤ x →
      HasDerivWithinAt (fun y => countProb τ T (k + 1) y)
        (T * countProb τ T (k + 1) x + vecMulVec (exitVec T) τ * countProb τ T k x)
        (Set.Ici 0) x) ∧
    countProb τ T 0 0 = 1 ∧
    (∀ k : ℕ, countProb τ T (k + 1) 0 = 0) ∧
    (∀ z : ℝ, |z| ≤ 1 → ∀ x : ℝ, 0 ≤ x →
      HasSum (fun k : ℕ => z ^ k • countProb τ T k x)
        (NormedSpace.exp (x • (T + z • vecMulVec (exitVec T) τ)))) := by sorry

end MatrixAnalytic.PHRenewal
