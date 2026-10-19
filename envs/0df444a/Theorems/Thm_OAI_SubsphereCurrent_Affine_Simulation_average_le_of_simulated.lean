-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Affine_Simulation_average_le_of_simulated
-- name    : OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:58:35.811013+00:00
-- url     : https://prove2.me/theorems/b1664447-a676-4905-98bb-f7e8eb55e787
-- title:
--   Angular success on an affine slice of the sphere is bounded by simulated streams in the slice subspace
-- statement:
--   Let $d,n\in\mathbb N$. An *affine test* $A$ of dimension $n$ in $\mathbb R^d$ consists of a linear subspace $H\subseteq\mathbb R^d$ with $\dim H=n$, a center $c\in H^\perp$ and a radius $r>0$ with $\|c\|^2+r^2=1$; assume $H\ne\{0\}$. For $s$ in the unit sphere $S_H$ of $H$ the point $c+rs$ is a unit vector, so $s\mapsto c+rs$ parametrizes the slice of the unit sphere $S^{d-1}$ by the affine subspace $c+H$. Write $\sigma_H$ for the uniform (normalized surface) measure on $S_H$, $\gamma_F$ for the standard Gaussian measure on a Euclidean space $F$, and $P_H$ for the orthogonal projection onto $H$.
--
--   A *randomized $T$-step stream* $L$ on a Euclidean space $F$ with finite nonempty state set $J$ has an initial distribution $\pi_0$ on $J$, transition probabilities $P_t(q'\mid q,(x,y))$ for $t\in\mathbb N$, $q,q'\in J$, $(x,y)\in F\times\mathbb R$, and output probability measures $\mu_q$ on $F$. On a target $u\in F$ and rows $x\in F^T$ it draws $Q_0\sim\pi_0$, then $Q_t\sim P_t(\cdot\mid Q_{t-1},(x_t,\langle x_t,u\rangle))$ for $t=1,\dots,T$, and outputs $Y\sim\mu_{Q_T}$. Its angular and Euclidean successes are
--   $$\mathrm{Ang}^L_\varepsilon(u,x)=\Pr\big[\arccos\langle Y,u\rangle\le\varepsilon\big],\qquad \mathrm{Succ}^L_\eta(u,x)=\Pr\big[\|Y-u\|\le\eta\big].$$
--   The stream has *Borel rules* if every map $(x,y)\mapsto P_t(q'\mid q,(x,y))$ is Borel measurable.
--
--   Given a stream $L$ on $\mathbb R^d$ and $w=(w_1,\dots,w_T)\in(H^\perp)^T$, the *simulated stream* $L^{A,w}$ on $H$ has the same states and initial distribution; at step $t$ it turns an observation $(x,y)\in H\times\mathbb R$ into the row $v=x+w_t\in\mathbb R^d$ with label $\langle v,c\rangle+ry$ and applies the transition of $L$ to $(v,\langle v,c\rangle+ry)$; in state $q$ it outputs the image of $\mu_q$ under $u\mapsto r^{-1}P_H(u-c)$.
--
--   **Theorem.** Let $L$ be a $T$-step stream on $\mathbb R^d$ with Borel rules whose output measures live on the unit sphere ($\|u\|=1$ for $\mu_q$-almost every $u$, for every state $q$). Let $\varepsilon\in\mathbb R$ and $B\in[0,\infty]$, and suppose that for every $w\in(H^\perp)^T$
--   $$\int_{S_H\times H^T}\mathrm{Succ}^{L^{A,w}}_{\varepsilon/r}(s,x)\,d\big(\sigma_H\otimes\gamma_H^{\otimes T}\big)(s,x)\le B .$$
--   Then
--
--   $$
--   \int_{S_H\times(\mathbb R^d)^T}\mathrm{Ang}^{L}_{\varepsilon}\big(c+rs,\,x\big)\,d\big(\sigma_H\otimes\gamma_{\mathbb R^d}^{\otimes T}\big)(s,x)\;\le\;B .
--   $$
--
--   The theorem reduces estimating a random point of an affine slice of $S^{d-1}$ to angular accuracy $\varepsilon$, with Gaussian rows in $\mathbb R^d$, to estimating a uniform point of the lower-dimensional sphere $S_H$ to Euclidean accuracy $\varepsilon/r$, with Gaussian rows in $H$. The components $w$ of the rows orthogonal to $H$ enter only as fixed parameters of the simulated stream, not as additional samples: the simulated stream reads exactly $T$ observations and has the same states. In the development, the hypothesis is then supplied by the general finite-memory stream bound in dimension $n$.
--
--   **Formalization Note** The simulated stream is `Simulation.stream A L w`; its kernel with time index $t$ uses the vector `w (t-1)` when $t-1<T$ (natural subtraction) and $0$ otherwise, which only matters at the times $t=1,\dots,T$ used by a run. The sphere measures are the normalized `volume.toSphere`, and the subspace $H$ is assumed `Nontrivial`; the state type carries a measurable structure with measurable singletons. The integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean#L585-L606

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Affine OAI.SubsphereCurrent.Affine.Simulation
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
attribute [local instance] OAI.SubsphereCurrent.Affine.Simulation.affineSimulationSphereLaw_probability
variable {d n : ℕ} (A : Test d n) [Nontrivial A.space]
  {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (L : Fixed.Stream (OAI.SubsphereCurrent.Affine.Vector d) J T)

theorem OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated (hL : L.BorelRules)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) (ε : ℝ) (B : ℝ≥0∞)
    (hb : ∀ w : Fin T → A.spaceᗮ,
      (∫⁻ z : Sphere A.space × (Fin T → A.space),
        (stream A L w).euclideanSuccess (ε/A.radius) z.1.val z.2
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)) ≤ B) :
    (∫⁻ z : Sphere A.space × (Fin T → OAI.SubsphereCurrent.Affine.Vector d),
      L.angularSuccess ε (A.point z.1) z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw (OAI.SubsphereCurrent.Affine.Vector d) T)) ≤ B := by sorry
