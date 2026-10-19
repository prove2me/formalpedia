-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_localized_routing_bound
-- name    : OAI.SubsphereRegression.localized_routing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:32:17.024526+00:00
-- url     : https://prove2.me/theorems/06fac393-fda0-43bd-87fb-f4885c87148a
-- title:
--   Localized routing bound for measures with polynomial ball growth
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d\ge1$ with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$. For a finite Borel measure $\nu$ on $E$ and $m\in\mathbb{N}$, the *projection law* $P_{\nu,m}$ is the image of $\gamma_E^{\otimes m}\otimes\nu$ under $(A,t)\mapsto\bigl(A,(\langle t,A_i\rangle)_{i=1}^m\bigr)$, a measure on the observation space $E^m\times\mathbb{R}^m$ (rows and noiseless labels). For $a\in\mathbb{N}$ and $C\in[0,\infty]$, say that $\nu$ has *polynomial ball growth* $(a,C)$ if $\nu(\bar B(z,r))\le C\,r^{a}$ for all $z\in E$ and all $r>0$, where $\bar B(z,r)$ is the closed ball.
--
--   Let $a,m,n\in\mathbb{N}$ satisfy $a\le d$, $m\le d$, $n\ge1$ and $n+m\le a$, and let $0<C<\infty$. Let $J$ be a finite set carrying a $\sigma$-algebra in which singletons are measurable, let $(\nu_j)_{j\in J}$ be finite Borel measures on $E$, each with polynomial ball growth $(a,C)$, and let $\varphi:E^m\times\mathbb{R}^m\to J$ be measurable. Then for every center $z\in E$ and every radius $r>0$,
--
--   $$
--   \sum_{j\in J}P_{\nu_j|_{\bar B(z,r)},\,m}\bigl(\{x:\varphi(x)=j\}\bigr)\;\le\;32768^{d}\,|J|^{1/(n+1)}\,C\,r^{a},
--   $$
--
--   where $\nu_j|_{\bar B(z,r)}$ is the restriction of $\nu_j$ to $\bar B(z,r)$.
--
--   This is the scale-free form of the routing bound: on a ball of radius $r$, the total mass that a $J$-valued rule routes to the "matching" states exceeds the single-measure bound $C r^a$ only by the factor $32768^d|J|^{1/(n+1)}$. It is exactly what is needed to show that one block of a finite-state streaming computation multiplies the polynomial-growth constant of a weighted measure by at most this factor.
--
--   **Formalization Note** Polynomial ball growth is `PolynomialMass (ν j) a C`, with the natural-number power $r^a$; the hypotheses $C\ne0$ and $C\ne\infty$ express $0<C<\infty$. All quantities are extended nonnegative reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Blocks.lean#L309-L337

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.localized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : ∀ j, PolynomialMass (ν j) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ)
    (z : E) {r : ℝ} (hr : 0 < r) :
    (∑ j, projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
        C * ENNReal.ofReal (r^a) := by sorry
