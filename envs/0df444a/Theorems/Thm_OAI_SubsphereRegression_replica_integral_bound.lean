-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_replica_integral_bound
-- name    : OAI.SubsphereRegression.replica_integral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:12:15.993984+00:00
-- url     : https://prove2.me/theorems/bbbadfce-6c88-4d99-a0f3-c86ebae4bb7f
-- title:
--   Exponential bound on inverse Gram–Schmidt moments of independent samples under a local mass bound
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a finite measure on $E$ and let $a\in\mathbb{R}$. Assume that $\nu$ satisfies the *local mass bound with exponent $a$*, that is, $\nu(\bar B(t,r))\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$, where $\bar B(t,r)$ is the closed ball and $\operatorname{supp}\nu$ is the support of $\nu$ (the set of points all of whose neighbourhoods have positive $\nu$-measure); assume also that $\operatorname{supp}\nu\subseteq\bar B(0,1)$.
--
--   Fix $m\in\mathbb{N}$ and a base point $p\in E$. For $n\in\mathbb{N}$ and $v=(v_0,\dots,v_{n-1})\in E^{n}$ let $u_0,\dots,u_{n-1}$ be the Gram–Schmidt vectors of the differences $v_0-p,\dots,v_{n-1}-p$ (the $i$-th one is $v_i-p$ minus its orthogonal projection onto the span of the earlier differences), so that $\|u_i\|$ is the distance from $v_i$ to the affine subspace through $p,v_0,\dots,v_{i-1}$. Define the replica weight and the constant
--   $$W_{m,p}(v)=\prod_{i=0}^{n-1}\|u_i\|^{-m},\qquad K_{\nu,a,m}=\nu(E)+3^{\dim E}\,4^{a}\,2^{m+1}$$
--   (see the Formalization Note for vanishing $u_i$). If $n+m\le a$, then, with $\nu^{\otimes n}$ the product measure on $E^{n}$,
--   $$\int_{E^{n}}W_{m,p}(v)\,d\nu^{\otimes n}(v)\le K_{\nu,a,m}^{\,n}.$$
--
--   Since $\prod_i\|u_i\|^{2}$ is the Gram determinant $\det\bigl(\langle v_i-p,v_j-p\rangle\bigr)_{i,j}$, for affinely independent $p,v_0,\dots,v_{n-1}$ the weight $W_{m,p}(v)$ is the $(-m/2)$-th power of this determinant, i.e. an inverse power of the volume of the simplex they span. The theorem therefore bounds negative moments of Gram determinants of $n$ independent samples from $\nu$, measured from a fixed further replica $p$, by a constant that is exponential in $n$. Through a replica expansion, such bounds control integer moments of smoothed densities of Gaussian measurements of a random point drawn from $\nu$.
--
--   **Formalization Note** The weight is `replicaWeight m p v`, the product over `i` of `ENNReal.ofReal ((‖u i‖)⁻¹ ^ m)`; Lean's real inverse satisfies `0⁻¹ = 0`, so a vanishing Gram–Schmidt vector contributes the factor $0^{m}$ (that is $0$ if $m\ge1$ and $1$ if $m=0$) rather than $+\infty$. The constant is `replicaConstant ν a m`, with $4^{a}$ a real power, and the hypothesis is `(n : ℝ) + m ≤ a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gram.lean#L240-L275

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by sorry
