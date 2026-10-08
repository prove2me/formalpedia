-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_mpec_mfcq_posLinIndep
-- name    : MPECRelax.ScholtesMFCQ.mpec_mfcq_posLinIndep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:34.949837+00:00
-- url     : https://prove2.me/theorems/ee50d8ed-a7df-447f-88b1-7ac9af81cd7a
-- title:
--   Proof of Theorem 3.2, p. 11 — MPEC-MFCQ gives positive-linear independence of the TNLP gradients at x*
-- statement:
--   Let $x^*$ be feasible for the MPEC (1) and let MPEC-MFCQ hold at $x^*$. Then the gradients
--   $$\{\nabla g_i(x^*)\mid i\in I_g\}\cup\big\{\{\nabla h_i(x^*)\mid i=1,\dots,p\}\cup\{\nabla G_i(x^*)\mid i\in I_{00}\cup I_{0+}\}\cup\{\nabla H_i(x^*)\mid i\in I_{00}\cup I_{+0}\}\big\}$$
--   are positive-linearly independent, where (as on p. 7 of the paper) the inner braces mark the vectors without sign constraint. Explicitly: if $\lambda\in\mathbb R^m$, $\lambda\ge 0$, $\lambda_i=0$ for $i\notin I_g$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ with $\gamma_i=0$ for $i\notin I_{00}\cup I_{0+}$ and $\nu_i=0$ for $i\notin I_{00}\cup I_{+0}$, and
--   $$\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)+\sum_{i=1}^l\gamma_i\nabla G_i(x^*)+\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--   then $\lambda=0$, $\mu=0$, $\gamma=0$ and $\nu=0$.
--
--   This is the first step of the proof of Theorem 3.2: MPEC-MFCQ, read through Remark 2.2 for the tightened program TNLP$(x^*)$, is a positive-linear independence condition.
--
--   **Formalization Note.** Indices are 0-based (`Fin m`, `Fin p`, `Fin l`). The sign of the $\gamma$ and $\nu$ terms is immaterial because they are unconstrained.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 11, proof of Theorem 3.2 (display after (6))

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- Proof of Theorem 3.2 (p. 11): under MPEC-MFCQ at a feasible `xs`, the family
`{∇g_i(xs) | i ∈ I_g} ∪ {{∇h_i(xs) | all i} ∪ {∇G_i(xs) | i ∈ I_00 ∪ I_0+} ∪
{∇H_i(xs) | i ∈ I_00 ∪ I_+0}}` is positive-linearly independent, the sign constraint
being on the `∇g_i` only: a vanishing combination with `lam ≥ 0` has all coefficients zero. -/
theorem mpec_mfcq_posLinIndep {n m p l : ℕ} (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n)
    (hfeas : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs) :
    ∀ (lam : Fin m → ℝ) (mu : Fin p → ℝ) (γ ν : Fin l → ℝ),
      (∀ i, 0 ≤ lam i) → (∀ i ∉ P.Ig xs, lam i = 0) →
      (∀ i ∉ P.I00 xs ∪ P.I0p xs, γ i = 0) → (∀ i ∉ P.I00 xs ∪ P.Ip0 xs, ν i = 0) →
      ∑ i, lam i • gradient (P.g i) xs + ∑ i, mu i • gradient (P.h i) xs +
          ∑ i, γ i • gradient (P.G i) xs + ∑ i, ν i • gradient (P.H i) xs = 0 →
      lam = 0 ∧ mu = 0 ∧ γ = 0 ∧ ν = 0 := by sorry

end MPECRelax.ScholtesMFCQ
