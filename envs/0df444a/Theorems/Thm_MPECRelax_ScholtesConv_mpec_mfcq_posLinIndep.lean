-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_mpec_mfcq_posLinIndep
-- name    : MPECRelax.ScholtesConv.mpec_mfcq_posLinIndep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:30.46356+00:00
-- url     : https://prove2.me/theorems/519e4ad1-2961-4d28-816d-04bcbafbb171
-- title:
--   Proof of Theorem 3.2, p. 11 — MPEC-MFCQ implies positive-linear independence of the TNLP gradients
-- statement:
--   Let $x^*$ be feasible for the MPEC (1) and let MPEC-MFCQ hold at $x^*$. Then the family
--   $$\{\nabla g_i(x^*)\mid i\in I_g\}\cup\big\{\{\nabla h_i(x^*)\mid i=1,\dots,p\}\cup\{\nabla G_i(x^*)\mid i\in I_{00}\cup I_{0+}\}\cup\{\nabla H_i(x^*)\mid i\in I_{00}\cup I_{+0}\}\big\}$$
--   is positive-linearly independent, where only the $\nabla g_i$ carry a sign constraint. Concretely: if $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ satisfy $\lambda\ge0$, $\lambda_i=0$ for $i\notin I_g$, $\gamma_i=0$ for $i\notin I_{00}\cup I_{0+}$, $\nu_i=0$ for $i\notin I_{00}\cup I_{+0}$, and
--
--   $$\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma_i\nabla G_i(x^*)-\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--
--   then $\lambda=0$, $\mu=0$, $\gamma=0$ and $\nu=0$.
--
--   The proof of Theorem 3.1 reaches its contradiction by producing a nonzero multiplier vector of exactly this kind ("a contradiction to the prerequisite that MPEC-MFCQ holds in $x^*$").
--
--   **Formalization Note** The paper states the claim in the proof of Theorem 3.2; it is the MPEC-MFCQ instance of Remark 2.2. The minus signs in front of $\gamma$ and $\nu$ follow the stationarity conditions; since $\gamma,\nu$ are unrestricted in sign they do not change the content.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 11, proof of Theorem 3.2 (first display after (6))

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

namespace MPECRelax.ScholtesConv

theorem mpec_mfcq_posLinIndep {n m p l : ℕ} (P : MPEC n m p l) (xs : E n)
    (hxs : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs)
    (lam : Fin m → ℝ) (mu : Fin p → ℝ) (γ ν : Fin l → ℝ)
    (hlam_nonneg : ∀ i, 0 ≤ lam i) (hlam_supp : ∀ i ∉ P.Ig xs, lam i = 0)
    (hγ_supp : ∀ i ∉ P.I00 xs ∪ P.I0p xs, γ i = 0)
    (hν_supp : ∀ i ∉ P.I00 xs ∪ P.Ip0 xs, ν i = 0)
    (hsum : ∑ i, lam i • gradient (P.g i) xs + ∑ i, mu i • gradient (P.h i) xs
      - ∑ i, γ i • gradient (P.G i) xs - ∑ i, ν i • gradient (P.H i) xs = 0) :
    lam = 0 ∧ mu = 0 ∧ γ = 0 ∧ ν = 0 := by sorry

end MPECRelax.ScholtesConv
