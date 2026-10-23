-- Prove2me | Theorems.Thm_LagrangeRank_Debias_theorem_3_1
-- name    : LagrangeRank.Debias.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:47.725484+00:00
-- url     : https://prove2.me/theorems/f285108c-0b5c-4240-ba46-3b09dd9bd128
-- title:
--   Theorem 3.1, p. 17 — studentized coordinates and pairwise differences of the Lagrangian debiased estimator converge in distribution to N(0, 1)
-- statement:
--   Work on one probability space $(\Omega,\mathcal F,\mathbb P)$. For each sample size $n$ let $d_n$ be the dimension, $L_n(\omega,\cdot):\mathbb R^{d_n}\to\mathbb R$ the random loss, $f_n$ the constraint defining $C_n=\{\theta:f_n(\theta)=0\}$, $\theta^*_n$ the true parameter, $\widehat\theta_n$ the initial estimator, $\widehat\Omega_n$ an estimator of the inverse of $\mathbb E[\nabla^2L_n(\theta^*_n)]$ and $\Omega^*_n$ its (deterministic) target. Let $i_n\neq j_n$ be coordinates. Let
--   $$\widehat\theta^d=\widehat\theta-\widehat\Theta_{11}\nabla L(\widehat\theta)$$
--   be the Lagrangian debiased estimator (3.9), with $\widehat\Theta$ the block-inverse matrix of p. 16 built from $(\widehat\Omega,\nabla f(\widehat\theta))$, and $\Theta^*$ the same formula at $(\Omega^*,\nabla f(\theta^*))$. Let $\Sigma^*_{11}=\mathbb E[\nabla^2L(\theta^*)]$,
--   $$v_n=[\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}]_{j_nj_n},\qquad w_n=(e_{i_n}-e_{j_n})^\top\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}(e_{i_n}-e_{j_n}).$$
--
--   Assume:
--
--   1. Assumptions 3.1–3.4 and the standing assumptions $f(\theta^*)=0$, $f(\widehat\theta)=0$ (the structure `Assumptions`), with fixed constants $K,c_1,c_2,c_3,L_1,L_2$;
--   2. $r_1\to0$, $r_4\to0$ and $\sqrt n\big(r_1^2r_5+(r_1+r_4)(r_1^2+r_2)+r_1r_3\big)\to0$;
--   3. Assumption 3.5: $v_n\ge C$ and $w_n\ge C$ for some $C>0$ and all $n$, and
--   $$\sqrt n\,\frac{[\Theta^*_{11}\nabla L(\theta^*)]_{j}}{\sqrt{v_n}}\xrightarrow{d}N(0,1),\qquad \sqrt n\,\frac{[\Theta^*_{11}\nabla L(\theta^*)]_{i}-[\Theta^*_{11}\nabla L(\theta^*)]_{j}}{\sqrt{w_n}}\xrightarrow{d}N(0,1);$$
--   4. $\widehat\theta_n$, the entries of $\widehat\Omega_n$ and $\omega\mapsto\nabla L_n(\omega,\widehat\theta_n(\omega))$ are measurable.
--
--   Then
--   $$\sqrt n\,\frac{\widehat\theta^d_{j}-\theta^*_{j}}{\sqrt{v_n}}\xrightarrow{d}N(0,1)\qquad\text{and}\qquad \sqrt n\,\frac{(\widehat\theta^d_{i}-\theta^*_{i})-(\widehat\theta^d_{j}-\theta^*_{j})}{\sqrt{w_n}}\xrightarrow{d}N(0,1).$$
--
--   The theorem is the inferential core of the Lagrangian debiasing framework: it yields confidence intervals for single scores and for pairwise score differences under a general equality constraint, without inverting the (possibly singular) bordered Hessian.
--
--   **Formalization Note.** The paper's $\lesssim$ is read as "at most $K$ times the rate on events $E_n$ with $\mathbb P(E_n^c)\to0$", with $K$ and $c_1,c_2,c_3,L_1,L_2$ independent of $n$ (this is the paper's "$c_1,c_2,c_3,L_1,L_2=O(1)$"). $\|\nabla f\|_\infty$ is read as the $\ell_1$ norm of $\nabla f$, as in the proof of Corollary 3.1. The conditions $r_1,r_4\to0$ are recalled in the proof (p. 43); $f(\theta^*)=f(\widehat\theta)=0$ is the standing assumption $\theta^*,\widehat\theta\in C$ (p. 14); the variance lower bound is the condition under which Assumption 3.5 is stated; measurability is needed for convergence in distribution to make sense. The sample size, dimension $d_n$ and coordinates $i_n,j_n$ are sequences; all variables live on one probability space, and convergence in distribution is weak convergence of laws (`TendstoInDistribution`).
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 17, Theorem 3.1 (with Assumptions 3.1–3.5, pp. 16–17); proof in Appendix A.1, pp. 40–41

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open MeasureTheory ProbabilityTheory Matrix Filter Topology
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (d : ℕ → ℕ) (L : (n : ℕ) → Ω → (Fin (d n) → ℝ) → ℝ) (f : (n : ℕ) → (Fin (d n) → ℝ) → ℝ)
    (thetaStar : (n : ℕ) → Fin (d n) → ℝ) (thetaHat : (n : ℕ) → Ω → Fin (d n) → ℝ)
    (OmegaHat : (n : ℕ) → Ω → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (OmegaStar : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (r1 r2 r3 r4 r5 : ℕ → ℝ) (K c1 c2 c3 L1 L2 : ℝ) (E : ℕ → Set Ω)
    (i j : (n : ℕ) → Fin (d n)) (hij : ∀ n, i n ≠ j n)
    (hA : Assumptions P d L f thetaStar thetaHat OmegaHat OmegaStar
      r1 r2 r3 r4 r5 K c1 c2 c3 L1 L2 E)
    (hr1 : Tendsto r1 atTop (𝓝 0)) (hr4 : Tendsto r4 atTop (𝓝 0))
    (hscale : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (r1 n ^ 2 * r5 n + (r1 n + r4 n) * (r1 n ^ 2 + r2 n) + r1 n * r3 n)) atTop (𝓝 0))
    (hvar : ∃ C : ℝ, 0 < C ∧ ∀ n,
      C ≤ popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n) ∧
      C ≤ popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n))
    (hclt1 : TendstoInDistribution (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n)
        / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n)))
      atTop id (fun _ => P) (gaussianReal 0 1))
    (hclt2 : TendstoInDistribution (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        ((thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (i n)
          - (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n))
        / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)))
      atTop id (fun _ => P) (gaussianReal 0 1))
    (hmeas_hat : ∀ n, Measurable (thetaHat n))
    (hmeas_Om : ∀ n a b, Measurable (fun ω => OmegaHat n ω a b))
    (hmeas_grad : ∀ n, Measurable (fun ω => grad (L n ω) (thetaHat n ω))) :
    TendstoInDistribution (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n))
        / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n)))
      atTop id (fun _ => P) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        ((estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (i n) - thetaStar n (i n))
          - (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n)))
        / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)))
      atTop id (fun _ => P) (gaussianReal 0 1) := by sorry
end LagrangeRank.Debias
