-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_average_euclideanSuccess_zero_bound
-- name    : OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_zero_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:57:58.144703+00:00
-- url     : https://prove2.me/theorems/b99741f9-d0a2-479a-9bee-7da6c776b48c
-- title:
--   A stream without observations lands within $\eta$ of a uniform unit vector with probability at most $3\cdot4^D\eta^{D-1}$
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, $D=\dim E\ge1$, $S_E$ its unit sphere and $\sigma_E$ the uniform (normalized surface) probability measure on $S_E$. Let $J$ be a finite nonempty set of states.
--
--   Consider a randomized stream $L$ on $E$ with state set $J$ and **zero** observation steps. It consists of an initial distribution $\pi_0$ on $J$, transition probabilities $P_t(q'\mid q,(x,y))$ for $t\in\mathbb N$, $q,q'\in J$ and $(x,y)\in E\times\mathbb R$ (never used, since there are no steps), and output probability measures $\mu_q$ on $E$. On any target it draws $Q_0\sim\pi_0$ and outputs $Y\sim\mu_{Q_0}$; for $s\in E$ write $\mathrm{Succ}_\eta(s)=\Pr[\|Y-s\|\le\eta]$. Assume that $L$ has Borel rules, i.e. every map $(x,y)\mapsto P_t(q'\mid q,(x,y))$ is Borel measurable.
--
--   **Theorem.** If $0<\eta\le1$, then
--
--   $$
--   \int_{S_E}\mathrm{Succ}_\eta(s)\,d\sigma_E(s)\;\le\;3\cdot4^{D}\,\eta^{D-1}.
--   $$
--
--   So an estimator that has seen no data lands within distance $\eta$ of a uniformly random unit vector with probability at most of the order of the $\sigma_E$-measure of a spherical cap of radius $\eta$. In the affine estimate of the development this handles the case of zero observation blocks, where it avoids the per-block factor of the general stream bound.
--
--   **Formalization Note** The Lean statement integrates over $S_E\times E^0$ against $\sigma_E\otimes\gamma_E^{\otimes0}$, where $\gamma_E$ is the standard Gaussian measure; $E^0$ (`Fin 0 → E`) is a one-point space carrying a probability measure, so this is the displayed integral. Values lie in $[0,\infty]$ and the right side is `ENNReal.ofReal (3*4^D) * ENNReal.ofReal (η^(D-1))` with $D$ = `Module.finrank ℝ E`; `D-1` is natural subtraction, harmless as $D\ge1$. The state type carries a measurable structure with measurable singletons.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean#L492-L524

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
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}

theorem OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_zero_bound [Nontrivial E] (L : Stream E J 0) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫⁻ z : Sphere E × (Fin 0 → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E 0)) ≤
      ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) *
        ENNReal.ofReal (η^(Module.finrank ℝ E-1)) := by sorry
