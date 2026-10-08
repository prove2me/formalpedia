-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_exists_optimal_tight
-- name    : MomentDRO.WorstCov.exists_optimal_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:37:25.308603+00:00
-- url     : https://prove2.me/theorems/5d372971-12bf-44c1-94df-ae9cc820dc2e
-- title:
--   §5.2, proof of Proposition 3, p. 20 — (19) has an optimal solution satisfying (19b) with equality
-- statement:
--   Let $K\ge1$, $a,b\in\mathbb R^K$, $x,\hat\mu\in\mathbb R^n$, $\hat\Sigma\succ0$ and $\gamma_2>0$. The SDP (19) of p. 19 (with objective $\sum_k -a_kx^{\mathsf T}\lambda_k-b_k\nu_k$) has an optimal solution $X^*=\{(\Lambda_k^*,\lambda_k^*,\nu_k^*)\}_{k=1}^K$ for which constraint (19b) holds with equality:
--   $$\sum_{k=1}^K\Lambda_k^*=\gamma_2\hat\Sigma+\hat\mu\hat\mu^{\mathsf T}.$$
--   That is, $X^*$ is feasible, no feasible point has a larger objective value, and the sum of the matrices $\Lambda_k^*$ fills the whole budget $\gamma_2\hat\Sigma+\hat\mu\hat\mu^{\mathsf T}$.
--
--   This is the step where the largest covariance enters: the tight matrix constraint becomes the second moment of the worst-case distribution built from $X^*$.
--
--   **Formalization Note** The page starts from "an optimal assignment $X^*$"; the statement includes the existence of an optimum, which the page uses implicitly.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 20, §5.2, proof of Proposition 3, after (19d)

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem exists_optimal_tight {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) :
    ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ),
      Feasible19 μhat Sighat γ2 Lam lam nu ∧
        (∀ (Lam' : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam' : Fin K → Fin n → ℝ)
            (nu' : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam' lam' nu' →
            obj19 a b x lam' nu' ≤ obj19 a b x lam nu) ∧
        ∑ k, Lam k = γ2 • Sighat + Matrix.vecMulVec μhat μhat := by sorry

end MomentDRO.WorstCov
