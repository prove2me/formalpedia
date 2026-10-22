-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_uniformization
-- name    : MatrixAnalytic.PHRenewal.uniformization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:24.323823+00:00
-- url     : https://prove2.me/theorems/be6ec562-5549-4b60-8cbd-71798e1978a0
-- title:
--   Lemma 3.2.3 — uniformization: $P(\nu,x) = \sum_{m\ge\nu} e^{-cx}\frac{(cx)^m}{m!}K_{m\nu}$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be an irreducible PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and $\boldsymbol\tau\mathbf 1=1$, and let $P(\nu,x)$ be the matrix of probabilities $P_{ij}(\nu,x)=\mathrm P[N(x)=\nu,\ J(x)=j\mid N(0)=0,\ J(0)=i]$ of the PH renewal process. Define
--   $$c=\max\{|T_{ii}|: 1\le i\le n\},\qquad P=c^{-1}T+I,\qquad \boldsymbol p=c^{-1}\boldsymbol t,$$
--   and the matrices $K_{m,\nu}$ by $K_{m,\nu}=0$ for $m<\nu$, $K_{m,0}=P^m$, $K_{m+1,\nu+1}=PK_{m,\nu+1}+\boldsymbol p\boldsymbol\tau K_{m,\nu}$ $(m,\nu\ge0)$. Then $\boldsymbol p=\mathbf 1-P\mathbf 1$, and for all $\nu\ge0$ and $x\ge0$
--   $$P(\nu,x)=\sum_{m\ge\nu}e^{-cx}\frac{(cx)^m}{m!}K_{m\nu}. \tag{3.6}$$
--
--   The formula expresses $P(\nu,x)$ through a Poisson number of transitions of a discrete-time chain, which is how these probabilities are computed in practice.
--
--   **Formalization Note** The maximum is encoded by two hypotheses: $|T_{ii}|\le c$ for every $i$ and $|T_{ii}|=c$ for some $i$. The sum over $m\ge\nu$ is written as a convergent series (`HasSum`) over $m=j+\nu$, $j\ge0$. $P(\nu,x)$ is the probabilistic object of the definition `Counting`.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 67–68, Lemma 3.2.3, Eqs. (3.6)–(3.9)

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting
import Definitions.Def_MatrixAnalytic_PHRenewal_Uniformization

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem uniformization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T)
    (c : ℝ) (hc_ge : ∀ i, |T i i| ≤ c) (hc_attained : ∃ i, |T i i| = c) :
    unifExit T c = (fun _ => 1) - unifP T c *ᵥ (fun _ => 1) ∧
    ∀ ν : ℕ, ∀ x : ℝ, 0 ≤ x →
      HasSum
        (fun j : ℕ => (Real.exp (-c * x) * (c * x) ^ (j + ν) / ((j + ν).factorial : ℝ)) •
          unifK τ T c (j + ν) ν)
        (countProb τ T ν x) := by sorry

end MatrixAnalytic.PHRenewal
