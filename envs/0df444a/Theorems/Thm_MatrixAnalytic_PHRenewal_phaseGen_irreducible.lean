-- Prove2me | Theorems.Thm_MatrixAnalytic_PHRenewal_phaseGen_irreducible
-- name    : MatrixAnalytic.PHRenewal.phaseGen_irreducible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:30.236229+00:00
-- url     : https://prove2.me/theorems/567ffb19-ab73-4ce3-8b79-18088850f6a6
-- title:
--   Lemma 3.1.1 — if $(\boldsymbol\tau, T)$ is irreducible then $D = T + \boldsymbol t\cdot\boldsymbol\tau$ is irreducible
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a PH representation on $n$ phases with exit vector $\boldsymbol t=-T\mathbf 1$, satisfying (2.4)–(2.6), with $T$ nonsingular and no atom at $0$ ($\boldsymbol\tau\mathbf 1=1$). Suppose the representation is irreducible: every phase is transient (it has a path to the absorbing phase $0$) and useful (it can be reached from some phase $i$ with $\tau_i>0$). Then the generator of the phase process,
--   $$D = T + \boldsymbol t\cdot\boldsymbol\tau,$$
--   is irreducible: for all phases $i, j$ there is a finite path $i=a_0,a_1,\dots,a_r=j$ with $a_{s}\ne a_{s+1}$ and $D_{a_s a_{s+1}}>0$.
--
--   This is the fact that makes the stationary vector of the phase process unique (Lemma 3.1.3).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 63, Lemma 3.1.1

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix

namespace MatrixAnalytic.PHRenewal

theorem phaseGen_irreducible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    IsIrreducibleGen (phaseGen τ T) := by sorry

end MatrixAnalytic.PHRenewal
