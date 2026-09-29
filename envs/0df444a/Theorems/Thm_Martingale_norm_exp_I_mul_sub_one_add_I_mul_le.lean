-- Prove2me | Theorems.Thm_Martingale_norm_exp_I_mul_sub_one_add_I_mul_le
-- name    : Martingale.norm_exp_I_mul_sub_one_add_I_mul_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:01:23.909765+00:00
-- url     : https://prove2.me/theorems/f5e468f4-9c36-4502-a697-7819e898eb82
-- title:
--   $\left|e^{ix} - (1 + ix)\right| \le x^2$ for $|x| \le 1$
-- statement:
--   A quantitative second-order estimate: for real $x$ with $|x| \le 1$,
--
--   $$\bigl|e^{ix} - (1 + ix)\bigr| \;\le\; x^2 .$$
--
--   It is the complex exponential estimate $|e^{z} - 1 - z| \le |z|^2$, valid for $|z| \le 1$, specialised to the purely imaginary $z = ix$, where $|z| = |x|$.
--
--   **Where it is used.** McLeish's proof of the martingale central limit theorem replaces the characteristic function $e^{i\theta S_n}$ — which cannot be factored, since the summands are not independent — by the comparison product $\prod_k(1 + i\theta Z_k)$, whose expectation is exactly $1$ by the martingale property. This lemma is what quantifies the substitution: each factor $1 + i\theta Z_k$ agrees with $e^{i\theta Z_k}$ to first order, with an error of size $O(|\theta Z_k|^2)$.
--
--   That the error is *quadratic* is precisely what the argument needs. The first-order terms cancel exactly, so the ratio $e^{i\theta z}/(1 + i\theta z)$ carries no linear term and its logarithm begins at $-\theta^2z^2/2$; summing over $k$ produces $-\tfrac{\theta^2}{2}\sum_k Z_k^2$, which the limiting-variance hypothesis converts into the Gaussian exponent $-\theta^2\sigma^2/2$. Any comparison factor agreeing with $e^{i\theta z}$ only to zeroth order would leave a linear term and destroy the identification.
--
--   The hypothesis $|x| \le 1$ is the range in which the underlying exponential estimate holds with constant $1$; in the application it is supplied by the negligibility of the increments, which makes $|\theta Z_k|$ uniformly small for large $n$.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem Martingale.norm_exp_I_mul_sub_one_add_I_mul_le (x : ℝ) (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x)‖ ≤ x ^ 2 := by sorry
