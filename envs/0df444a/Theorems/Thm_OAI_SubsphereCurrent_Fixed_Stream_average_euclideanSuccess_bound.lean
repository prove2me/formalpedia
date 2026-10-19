-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_average_euclideanSuccess_bound
-- name    : OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:57:28.13448+00:00
-- url     : https://prove2.me/theorems/fe85cf9c-af7e-4259-afda-632f4a8777f8
-- title:
--   Euclidean success bound for randomized finite-state streams with Gaussian measurements of a random unit vector
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, and put $D=\dim E\ge1$. Write $S_E=\{u\in E:\|u\|=1\}$ for its unit sphere, $\sigma_E$ for the uniform (normalized surface) probability measure on $S_E$, and $\gamma_E$ for the standard Gaussian measure on $E$. Let $J$ be a finite nonempty set of memory states and let $T\ge0$ be the number of observations.
--
--   A *randomized $T$-step stream* $L$ on $E$ with state set $J$ consists of an initial distribution $\pi_0$ on $J$, transition probabilities $P_t(q'\mid q,(x,y))$ for every time $t\in\mathbb N$, states $q,q'\in J$ and observation $(x,y)\in E\times\mathbb R$, and an output probability measure $\mu_q$ on $E$ for every state $q$. Given a vector $s\in E$ and rows $x=(x_1,\dots,x_T)\in E^T$, the stream draws $Q_0\sim\pi_0$, then for $t=1,\dots,T$ draws $Q_t\sim P_t(\cdot\mid Q_{t-1},(x_t,\langle x_t,s\rangle))$, and finally outputs $Y\sim\mu_{Q_T}$. Its *Euclidean success* at radius $\eta$ is $\mathrm{Succ}_\eta(s,x)=\Pr\big[\|Y-s\|\le\eta\big]$. The stream has *Borel rules* if every map $(x,y)\mapsto P_t(q'\mid q,(x,y))$ is Borel measurable on $E\times\mathbb R$.
--
--   **Theorem.** Assume $L$ has Borel rules. Let $\eta>0$ and let $a,q$ be natural numbers with $2a\le D-1$, $q\ge2$ and $2q\le a$. Then
--
--   $$
--   \int_{S_E\times E^T}\mathrm{Succ}_\eta(s,x)\,d\big(\sigma_E\otimes\gamma_E^{\otimes T}\big)(s,x)\;\le\;3\cdot4^{D}\,\eta^{a}\,\Big(32768^{D}\,|J|^{1/q}\Big)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   In words: when the hidden vector $s$ is uniform on the sphere and the $T$ rows are independent standard Gaussian vectors, a stream with $|J|$ memory states outputs a point within distance $\eta$ of $s$ only with probability of order $\eta^{a}$, up to a factor $32768^{D}|J|^{1/q}$ for each block of $q$ observations. This is the generic finite-memory estimate of the development; with suitable choices of $q$ and $a$ it gives the bound for streams with $2^{d^2}$ states in the fixed-dimension estimate and the bound for the simulated streams in the affine estimate.
--
--   **Formalization Note** The left side is a lower Lebesgue integral of a $[0,\infty]$-valued function: `L.euclideanSuccess η s x` is the measure of the closed ball of radius $\eta$ around $s$ under the output law `L.estimateLaw s x`. The right side is `ENNReal.ofReal (3*4^D) * ENNReal.ofReal (η^a) * streamFactor q ^ (T/q+1)` (with $D$ standing for `Module.finrank ℝ E`), where `streamFactor q` $=32768^D|J|^{1/q}$ uses a real power and `T/q` is truncated natural division; `D-1` is natural subtraction, harmless because $D\ge1$. The $t$-th observation is processed by the kernel with time index $t$. The state type carries a measurable structure with measurable singletons.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean#L228-L265

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Fixed OAI.SubsphereCurrent.Fixed.Stream
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

theorem OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound [Nontrivial E] (L : Stream E J T) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) {a q : ℕ}
    (ha : 2*a ≤ Module.finrank ℝ E-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    (∫⁻ z : Sphere E × (Fin T → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E T)) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := E) (J := J) q ^ (T/q+1) := by sorry
