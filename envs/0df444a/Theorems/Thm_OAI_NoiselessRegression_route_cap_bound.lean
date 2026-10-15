-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_route_cap_bound
-- name    : OAI.NoiselessRegression.route_cap_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:43:43.361112+00:00
-- url     : https://prove2.me/theorems/b26afe00-d8f2-46e2-a169-8276f6363c04
-- title:
--   Cap bound for the output of a $k$-step finite-state route fed with noiseless Gaussian observations of a random unit vector
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, $D=\dim_{\mathbb R}E\ge1$, $\gamma_E$ the standard Gaussian measure on $E$, $S=\{s\in E:\|s\|=1\}$ the unit sphere, and $\sigma$ the uniform probability measure on $S$ (surface measure normalized to total mass $1$). Let $J$ be a nonempty finite set with a $\sigma$-algebra in which singletons are measurable, let $\delta_n:J\times(E\times\mathbb R)\to J$ ($n\in\mathbb N$) be transition maps such that $\delta_n(j,\cdot):E\times\mathbb R\to J$ is measurable for all $n,j$, and let $y:J\to E$ be an arbitrary map assigning a point of $E$ to each state.
--
--   For $k\in\mathbb N$, $j\in J$, rows $A=(A_1,\dots,A_k)\in E^k$ and $s\in E$, let $R^{0,k}_\delta(j;A,\langle s,A\rangle)$ be the state reached from $j$ by feeding the observations $(A_i,\langle s,A_i\rangle)$, $i=1,\dots,k$, through $\delta_1,\dots,\delta_k$: $j_0=j$, $j_i=\delta_i\bigl(j_{i-1},(A_i,\langle s,A_i\rangle)\bigr)$, and $R^{0,k}_\delta(j;A,\langle s,A\rangle)=j_k$. For an integer $q\ge1$ put $K_q=32768^{D}\,|J|^{1/q}$.
--
--   Let $\varepsilon>0$ and let $a,q\in\mathbb N$ satisfy $2a\le D-1$, $q\ge2$ and $2q\le a$. Then for every $k\in\mathbb N$ and every $j\in J$,
--
--   $$
--   (\sigma\otimes\gamma_E^{\otimes k})\Bigl\{(s,A)\in S\times E^k:\ \bigl\|s-y\bigl(R^{0,k}_\delta(j;A,\langle s,A\rangle)\bigr)\bigr\|\le\varepsilon\Bigr\}\le3\cdot4^{D}\,\varepsilon^{a}\,K_q^{\lfloor k/q\rfloor+1}.
--   $$
--
--   Here $s$ is a uniformly random unit vector, $A_1,\dots,A_k$ are independent standard Gaussian rows observed together with their noiseless labels $\langle s,A_i\rangle$, and the finite-state machine outputs the point $y(\cdot)$ attached to its final state. The theorem bounds the probability that this output lies within distance $\varepsilon$ of $s$: the factor $\varepsilon^a$ reflects the small measure of a spherical cap of radius $\varepsilon$, while the number of states enters only through $|J|^{(\lfloor k/q\rfloor+1)/q}$.
--
--   **Formalization Note** $\sigma$ is `sphereLaw`, $K_q$ is `streamFactor q` (with real exponent $1/q$), $\lfloor k/q\rfloor$ is the natural-number division `k/q`, and the hypothesis $2a\le D-1$ is stated with truncated subtraction, which is harmless because $D\ge1$ for nontrivial $E$. The numerical factor appears as `ENNReal.ofReal (3*4^D) * ENNReal.ofReal (ε^a)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Caps.lean#L72-L109

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Definitions.Def_OAI_Probability_GaussianRegression_Caps

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

theorem OAI.NoiselessRegression.route_cap_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by sorry
