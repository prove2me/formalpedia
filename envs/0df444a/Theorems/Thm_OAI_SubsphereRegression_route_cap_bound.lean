-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_route_cap_bound
-- name    : OAI.SubsphereRegression.route_cap_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:36:19.628985+00:00
-- url     : https://prove2.me/theorems/9e5fce7d-6e8f-43e6-a80f-582091cafb20
-- title:
--   A finite-state stream rarely lands within $\varepsilon$ of a uniformly random unit vector
-- statement:
--   Let $E$ be a nonzero real inner product space of finite dimension $d$ with its Borel $\sigma$-algebra, let $\gamma_E$ be its standard Gaussian measure, and let $\sigma$ be the normalized surface (uniform probability) measure on the unit sphere $S=\{s\in E:\|s\|=1\}$. Let $J$ be a nonempty finite set carrying a $\sigma$-algebra in which singletons are measurable, and let $\delta=(\delta_t)_{t\in\mathbb{N}}$, $\delta_t:J\times(E\times\mathbb{R})\to J$, be a transition rule such that every map $\delta_t(j,\cdot)$ is measurable. For $k\in\mathbb{N}$ and $j\in J$, the *route* $R_{0,k}(j;\cdot):E^k\times\mathbb{R}^k\to J$ sends $(A,b)$ to the state $j_k$ given by $j_0=j$ and $j_i=\delta_i(j_{i-1},(A_i,b_i))$ for $i=1,\dots,k$. For $q\in\mathbb{N}$ put $K_q=32768^d\,|J|^{1/q}$.
--
--   Let $y:J\to E$ assign a point to every state, let $\varepsilon>0$, and let $a,q\in\mathbb{N}$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$. Then for every $k\in\mathbb{N}$ and every $j\in J$,
--
--   $$
--   (\sigma\otimes\gamma_E^{\otimes k})\Bigl\{(s,A)\in S\times E^k:\ \bigl\|s-y\bigl(R_{0,k}(j;A,(\langle s,A_i\rangle)_{i=1}^k)\bigr)\bigr\|\le\varepsilon\Bigr\}\;\le\;3\cdot4^{d}\,\varepsilon^{a}\,K_q^{\lfloor k/q\rfloor+1}.
--   $$
--
--   Read $y(R_{0,k}(j;\cdot))$ as the point announced by a finite-state algorithm with state set $J$ that starts in state $j$, reads $k$ Gaussian rows $A_i$ together with the labels $\langle s,A_i\rangle$, and outputs a point depending only on its final state. The theorem bounds the probability, over a uniformly random hidden unit vector $s$ and the rows, that this output lies within distance $\varepsilon$ of $s$: it decays like $\varepsilon^a$ with $a$ of order $d$, at the cost of one factor $K_q$ per block of $q$ rows. This is the single-seed, deterministic core of the success bound for finite-memory learners.
--
--   **Formalization Note** $\sigma$ is `sphereLaw` (the surface measure `volume.toSphere` divided by its total mass), the route is `streamRoute δ 0 k j`, $K_q$ is `streamFactor q`, and $\lfloor k/q\rfloor$ is natural-number division. The condition $2a\le d-1$ uses truncated subtraction, which is ordinary subtraction here since $d\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L344-L381

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

theorem OAI.SubsphereRegression.route_cap_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by sorry
