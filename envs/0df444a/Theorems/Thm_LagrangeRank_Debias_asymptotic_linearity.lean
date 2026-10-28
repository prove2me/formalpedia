-- Prove2me | Theorems.Thm_LagrangeRank_Debias_asymptotic_linearity
-- name    : LagrangeRank.Debias.asymptotic_linearity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:33.360984+00:00
-- url     : https://prove2.me/theorems/f110b135-e79e-49f4-be96-67d527ca98fd
-- title:
--   Proof of Theorem 3.1, pp. 40–41, closing displays — studentized θ̂ᵈ equals minus the studentized score plus o_P(1)
-- statement:
--   Work on one probability space $(\Omega,\mathcal F,\mathbb P)$. For each sample size $n$ let $d_n$ be the dimension, $L_n(\omega,\cdot)$ the random loss, $f_n$ the constraint, $\theta^*_n$ the true parameter, $\widehat\theta_n$ the initial estimator, $\widehat\Omega_n$ the inverse-Hessian estimator and $\Omega^*_n$ its target, and let $i_n\neq j_n$ be coordinates. Assume Assumptions 3.1–3.4 with the standing assumptions (the structure `Assumptions`, with rates $r_1,\dots,r_5$, constants $K,c_1,c_2,c_3,L_1,L_2$ and events $E_n$), $r_1\to0$, $r_4\to0$, the scaling condition
--   $$\sqrt n\big(r_1^2r_5+(r_1+r_4)(r_1^2+r_2)+r_1r_3\big)\to0,$$
--   and the variance lower bound of Assumption 3.5: for some $C>0$ and all $n$, $v_n=[\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}]_{j_nj_n}\ge C$ and $w_n=(e_{i_n}-e_{j_n})^\top\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}(e_{i_n}-e_{j_n})\ge C$. Then, in probability,
--   $$\sqrt n\,\frac{\widehat\theta^d_{j}-\theta^*_{j}}{\sqrt{v_n}}+\sqrt n\,\frac{[\Theta^*_{11}\nabla L(\theta^*)]_{j}}{\sqrt{v_n}}\to0,$$
--   $$\sqrt n\,\frac{(\widehat\theta^d_{i}-\theta^*_{i})-(\widehat\theta^d_{j}-\theta^*_{j})}{\sqrt{w_n}}+\sqrt n\,\frac{[\Theta^*_{11}\nabla L(\theta^*)]_{i}-[\Theta^*_{11}\nabla L(\theta^*)]_{j}}{\sqrt{w_n}}\to0,$$
--   with $i=i_n$, $j=j_n$, $\widehat\theta^d$ the debiased estimator (3.9) and $\Theta^*$ the block-inverse matrix of p. 16 at $(\Omega^*_n,\nabla f_n(\theta^*_n))$.
--
--   This is the "$=-\sqrt n[\Theta^*_{11}\nabla L(\theta^*)]_j/\sqrt{\cdots}+o_{\mathbb P}(1)$" step of the proof of Theorem 3.1; with Assumption 3.5 and Slutsky's lemma it gives the theorem.
--
--   **Formalization Note.** The page prints the normalization as $[\Theta^*_{11}\Sigma^*_{11}\Theta^*_{11}]_{jj}$, without the transpose that Theorem 3.1 and Assumption 3.5 carry; the theorem's normalization is used. $o_{\mathbb P}(1)$ is `TendstoInMeasure` to $0$. The variance lower bound is the condition under which Assumption 3.5 is stated; it is needed to divide the remainder by $\sqrt{v_n}$.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, pp. 40–41, proof of Theorem 3.1 (Appendix A.1), closing displays

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open MeasureTheory ProbabilityTheory Matrix Filter Topology
theorem asymptotic_linearity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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
      C ≤ popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) =>
        Real.sqrt (n : ℝ) *
          (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n))
          / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n))
        + Real.sqrt (n : ℝ) *
          (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n)
          / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n))) atTop 0 ∧
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) =>
        Real.sqrt (n : ℝ) *
          ((estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (i n) - thetaStar n (i n))
            - (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n)))
          / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n))
        + Real.sqrt (n : ℝ) *
          ((thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (i n)
            - (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n))
          / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)))
      atTop 0 := by sorry
end LagrangeRank.Debias
