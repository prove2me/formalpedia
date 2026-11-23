-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_upper_parameter_bounds
-- name    : LindbladTolerant.Testing.upper_parameter_bounds
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:59:46.391437+00:00
-- url     : https://prove2.me/theorems/b23c1a92-7f16-4869-9722-35fb47832380
-- title:
--   Algorithm 1 — positive time, explicit cost bound, and stored-copy sufficiency
-- statement:
--   Fix $k\ge1$ and thresholds $0\le\varepsilon_1<\varepsilon_2$, and write $\Delta=\varepsilon_2-\varepsilon_1$. Assume $C_k\ge1$, as supplied by the copy estimator of Theorem 4.3. The Algorithm 1 parameters satisfy $A_k>0$ and $T>0$, together with the explicit uniform cost estimate
--   $$T\le A_k\frac{\varepsilon_2}{\Delta^2},\qquad A_k=32768q_k^2(C_k+1).$$
--   Moreover, on every flag sequence reaching the intermediate decision branch,
--   $$\frac{\varepsilon_2}{2q_k}<\frac KT<2\varepsilon_2
--   \quad\Longrightarrow\quad K\ge R,$$
--   so the routine always has the $R$ stored successful outputs required by the functional estimator.
--
--   This packages the ceiling estimate $\lceil x\rceil<x+1$, the accuracy identity $\delta=\Delta/(32\varepsilon_2)$, and Eq.(97), while also supplying the positivity side conditions needed by the main reduction.
--
--   **Formalization Note** The storage statement is formulated for flag sequences of any finite length, not only the preset attempt count. The bound $C_k\ge1$ is an explicit arithmetic hypothesis so that this elementary statement need not assume the copy-estimator theorem itself.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Algorithm 1 and Theorem 5.1 proof, pp.26–28, specifically Eq.(97) on p.27 and Eq.(110) on p.28; the hypothesis C_k ≥ 1 is from Algorithm 1, p.26

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix
open LindbladTolerant.Testing

theorem LindbladTolerant.Testing.upper_parameter_bounds (k : ℕ) (hk : 1 ≤ k)
    (hC : 1 ≤ copyConstant k) :
    0 < upperConstant k ∧
    ∀ eps1 eps2 : ℝ, 0 ≤ eps1 → eps1 < eps2 →
      0 < totalTime k eps1 eps2 ∧
      totalTime k eps1 eps2 ≤ upperConstant k * eps2 / (eps2-eps1)^2 ∧
      ∀ {M : ℕ} (f : Fin M → Bool),
        eps2 / (2 * qConstant k) < (successCount f : ℝ) / totalTime k eps1 eps2 →
        (successCount f : ℝ) / totalTime k eps1 eps2 < 2*eps2 →
        retainedCount k eps1 eps2 ≤ successCount f := by sorry
