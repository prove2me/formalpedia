-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_prefix_route_cap_bound
-- name    : OAI.NoiselessRegression.prefix_route_cap_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:45:04.54663+00:00
-- url     : https://prove2.me/theorems/6442cb56-2ca6-4c4b-a048-06b3dd08438c
-- title:
--   Cap bound for a finite-state route that reads only a prefix of $T$ noiseless Gaussian samples
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, $D=\dim_{\mathbb R}E\ge1$, $\gamma_E$ the standard Gaussian measure on $E$, $S=\{s\in E:\|s\|=1\}$ the unit sphere, and $\sigma$ the uniform probability measure on $S$ (surface measure normalized to total mass $1$). Let $J$ be a nonempty finite set with a $\sigma$-algebra in which singletons are measurable, let $\delta_n:J\times(E\times\mathbb R)\to J$ ($n\in\mathbb N$) be transition maps such that $\delta_n(j,\cdot):E\times\mathbb R\to J$ is measurable for all $n,j$, and let $y:J\to E$ be an arbitrary map assigning a point of $E$ to each state.
--
--   For $k\in\mathbb N$, $j\in J$, rows $A=(A_1,\dots,A_k)\in E^k$ and $s\in E$, let $R^{0,k}_\delta(j;A,\langle s,A\rangle)$ be the state reached from $j$ by feeding the observations $(A_i,\langle s,A_i\rangle)$, $i=1,\dots,k$, through $\delta_1,\dots,\delta_k$: $j_0=j$, $j_i=\delta_i\bigl(j_{i-1},(A_i,\langle s,A_i\rangle)\bigr)$, and $R^{0,k}_\delta(j;A,\langle s,A\rangle)=j_k$. For an integer $q\ge1$ put $K_q=32768^{D}\,|J|^{1/q}$. For $x=(x_1,\dots,x_T)\in E^T$ and $k\le T$ write $x_{\le k}=(x_1,\dots,x_k)\in E^k$.
--
--   Let $\varepsilon>0$, let $a,q\in\mathbb N$ satisfy $2a\le D-1$, $q\ge2$ and $2q\le a$, and let $k\le T$ be natural numbers. Then for every $j\in J$,
--
--   $$
--   (\sigma\otimes\gamma_E^{\otimes T})\Bigl\{(s,x)\in S\times E^T:\ \bigl\|s-y\bigl(R^{0,k}_\delta(j;x_{\le k},\langle s,x_{\le k}\rangle)\bigr)\bigr\|\le\varepsilon\Bigr\}\le3\cdot4^{D}\,\varepsilon^{a}\,K_q^{\lfloor T/q\rfloor+1}.
--   $$
--
--   A learner that stops after $k\le T$ steps sees only a prefix of its $T$ samples. Because the right-hand side depends on $T$ but not on $k$, the bound is uniform over all possible stopping times $k\le T$, which is what a union bound over stopping times requires.
--
--   **Formalization Note** $\sigma$ is `sphereLaw`, $K_q$ is `streamFactor q` (with real exponent $1/q$), $\lfloor T/q\rfloor$ is the natural-number division `T/q`, the prefix is `fun i => x (Fin.castLE hk i)`, and $2a\le D-1$ uses truncated subtraction (harmless since $D\ge1$). The numerical factor appears as `ENNReal.ofReal (3*4^D) * ENNReal.ofReal (ε^a)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Transfer.lean#L59-L81

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
import Definitions.Def_OAI_Probability_GaussianRegression_Execution

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by sorry
