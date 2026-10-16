-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_comparison_resolvent_average
-- name    : OAI.DiagonalForms.System.comparison_resolvent_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:30:17.067166+00:00
-- url     : https://prove2.me/theorems/190b2870-3698-431a-9f47-1f36631abb7c
-- title:
--   Averaged resolvent-type weights $m / \int_0^1 R(q_\theta)\,d\theta$ are comparison weights
-- statement:
--   Let $D$ be a *diagonal-form system*: index sets $P$ (parameters), $I$ (source coordinates) and $J$ (target coordinates), labelling maps $\pi : I \to P$ and $\tau : J \to P$, a complex linear space $T \subseteq \mathbb{C}^I$ of test vectors and a complex-linear map $M : T \to \mathbb{C}^J$, such that every $z \in T$ is square-summable, only finitely many parameters $\pi(i)$ occur among the indices $i$ with $z_i \neq 0$, and $T$ is closed under the multipliers $(z_i)_i \mapsto (\omega(\pi(i))\, z_i)_i$ for every $\omega : P \to \mathbb{C}$. For a weight $w : P \to \mathbb{R}$ and $z \in T$ put $S_w(z) = \sum_{i \in I} w(\pi(i))\,|z_i|^2$. The weight $w$ is called a *comparison weight* for $D$ if $\sum_{j \in F} w(\tau(j))\,|(Mz)_j|^2 \le S_w(z)$ for every $z \in T$ and every finite set $F \subseteq J$.
--
--   Let $K$ be a compact metric space with its Borel $\sigma$-algebra, $\mu$ a finite measure on $K$, $c \ge 0$, and $r : K \to [0,1]$ continuous. For $q > 0$ define the resolvent weight
--   $$
--   R(q) = \frac{1}{q} + c + \int_K \frac{d\mu(k)}{1 + (q - 1)\,r(k)} .
--   $$
--
--   **Theorem.** Let $k_0 \in K$ and let $m, s, t : P \to \mathbb{R}$ be positive functions such that $m$, $m s$ and $m t$ are comparison weights for $D$. Then
--   $$
--   p \longmapsto \frac{m(p)}{\displaystyle\int_0^1 R\big((1-\theta)s(p) + \theta\,t(p)\big)\,d\theta}
--   $$
--   is a comparison weight for $D$.
--
--   This combines the resolvent closure property (the weight $m/R(q)$ inherits the comparison property from $m$ and $mq$) with averaging along the segment from $s$ to $t$, producing the averaged weights needed when the parameter $q$ itself is interpolated.
--
--   **Formalization Note** The system is `OAI.DiagonalForms.System P I J` with fields `sourceParam` ($\pi$), `targetParam` ($\tau$), `tests` ($T$) and `map` ($M$); $S_w$ is `D.sourceForm w` (a `tsum`, which converges because only finitely many parameter values occur) and "comparison weight" is `D.Comparison w`. $R(q)$ is `resolventWeight μ c r q` and the $\theta$-integral is over `UnitInterval = Set.Icc (0:ℝ) 1` with Lebesgue measure. Note $1 + (q-1)r(k) = (1 - r(k)) + q\,r(k) > 0$ for $q > 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L779-L814

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms

open OAI OAI.DiagonalForms OAI.DiagonalForms.System
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

theorem OAI.DiagonalForms.System.comparison_resolvent_average (k₀ : K) {m s t : P → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    (hm : ∀ p, 0 < m p) (hs : ∀ p, 0 < s p) (ht : ∀ p, 0 < t p)
    (hmc : D.Comparison m) (hsc : D.Comparison (fun p => m p*s p))
    (htc : D.Comparison (fun p => m p*t p)) :
    D.Comparison (fun p => m p / ∫ θ : UnitInterval,
      resolventWeight μ c r ((1-θ.val)*s p+θ.val*t p)) := by sorry
