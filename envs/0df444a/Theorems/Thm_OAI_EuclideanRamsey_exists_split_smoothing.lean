-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_exists_split_smoothing
-- name    : OAI.EuclideanRamsey.exists_split_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:03:04.371313+00:00
-- url     : https://prove2.me/theorems/011e9164-d786-4a67-bae1-34096c0e4c58
-- title:
--   Smooth bumps with small weighted negative part for a split second-order operator
-- statement:
--   Let $k,d\in\mathbb{N}$. Let $H$ be a finite-dimensional real inner product space with $\dim H\ge1$, and let $V$ be a finite-dimensional real normed space. Let $C$ and $Z$ be real $k\times k$ matrices and $R$ a real $k\times d$ matrix such that
--   $$
--   C=RR^{\top}+ZCZ^{\top}.
--   $$
--   Let $\Phi:\mathbb{R}^k\to H\times V$ be a linear isomorphism, let $(h_1,\dots,h_d)$ be an orthonormal basis of $H$, and let $z_1,\dots,z_k\in V$ be vectors such that the columns $R_{\cdot j}$ of $R$ and $Z_{\cdot j}$ of $Z$ satisfy
--   $$
--   \Phi(R_{\cdot j})=(h_j,0)\quad(1\le j\le d),\qquad \Phi(Z_{\cdot j})=(0,z_j)\quad(1\le j\le k).
--   $$
--   Write $\Phi_H(x)\in H$ for the first component of $\Phi(x)$, let $\mathbf e_1,\dots,\mathbf e_k$ be the standard basis of $\mathbb{R}^k$, and for a $C^2$ function $b:\mathbb{R}^k\to\mathbb{R}$ put
--   $$
--   L_Cb(x)=\frac12\sum_{j,l=1}^{k}C_{jl}\,D^2b(x)[\mathbf e_j,\mathbf e_l]=\frac12\sum_{j,l=1}^{k}C_{jl}\,\partial_j\partial_lb(x),
--   $$
--   where $D^2b(x)$ is the second Fréchet derivative. Then for every $\eta>0$ there is a $C^\infty$ function $b:\mathbb{R}^k\to\mathbb{R}$ with compact support such that $b\ge0$, $\int_{\mathbb{R}^k}b(x)\,dx>0$ and
--
--   $$
--   \int_{\mathbb{R}^k}\max\big(-L_Cb(x),\,0\big)\,\big\|\Phi_H(x)\big\|^2\,dx\;<\;\eta\int_{\mathbb{R}^k}b(x)\,dx,
--   $$
--
--   where the integrals are taken with respect to Lebesgue measure on $\mathbb{R}^k$.
--
--   The matrix $C$ is arbitrary, so $L_C$ need not be elliptic and $L_Cb$ may take both signs. The theorem says that one can nevertheless find nonnegative bumps for which the negative part of $L_Cb$, weighted by the squared horizontal coordinate $\|\Phi_H(x)\|^2$, is an arbitrarily small fraction of the mass of $b$. The splitting $C=RR^{\top}+ZCZ^{\top}$ separates a horizontal block, on which $L_C$ acts as half the Laplacian of $H$, from a vertical block, which can be scaled away. It is the analytic core of the smoothing step in the classification of Euclidean Ramsey configurations, where it is applied with $\Phi(x)=(Ux,\,x-RUx)$ for a matrix $U$ with $UCU^{\top}=I$.
--
--   **Formalization Note** $L_Cb$ is `secondOperator C (fun j => Pi.single j 1) b`, where `secondOperator C v f x = (1/2) * ∑ j, ∑ l, C j l * hessianB f x (v j) (v l)` and `hessianB` is the second Fréchet derivative. $\Phi$ is a continuous linear equivalence `e : (Fin k → ℝ) ≃L[ℝ] H × V`, and the orthonormal basis is indexed by `Fin d`, so in fact $d=\dim H\ge1$. The Borel $\sigma$-algebras assumed on $H$ and $V$ are used only inside the proof; for the $b$ produced, all integrands in the statement are continuous with compact support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean#L230-L323

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting

open OAI OAI.EuclideanRamsey
universe uDomain uAction uVertical uCodomain
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open scoped BigOperators
open Matrix MeasureTheory
open MeasureTheory
open MeasureTheory
open MeasureTheory Matrix
open scoped BigOperators

theorem OAI.EuclideanRamsey.exists_split_smoothing {k d : ℕ} {H : Type uAction} {V : Type uVertical}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
    (hn : 1 ≤ Module.finrank ℝ H)
    (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ)
    (hsplit : C = R*R.transpose+Z*C*Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] H×V) (eh : OrthonormalBasis (Fin d) ℝ H)
    (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (eh j,0))
    (hZ : ∀ j, e (fun l => Z l j) = (0,z j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∧
      (∫ x, max (-secondOperator C (fun j => Pi.single j 1) b x) 0 * ‖(e x).1‖^2) <
        η * ∫ x, b x := by sorry
