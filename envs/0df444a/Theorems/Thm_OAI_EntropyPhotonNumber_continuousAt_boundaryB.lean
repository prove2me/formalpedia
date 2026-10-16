-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_continuousAt_boundaryB
-- name    : OAI.EntropyPhotonNumber.continuousAt_boundaryB
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:23:15.133341+00:00
-- url     : https://prove2.me/theorems/408ed140-3dfc-4a82-a78c-60f46dfba301
-- title:
--   Continuity of the boundary function $\mathcal B$ at points of the positive real axis
-- statement:
--   Let $\operatorname{sinc}(z) = \sin z / z$ for $z \neq 0$ and $\operatorname{sinc}(0) = 1$ (an entire function), and let $\operatorname{ccot}(z) = \cos z / \operatorname{sinc}(z)$ (so $\operatorname{ccot}(z) = z\cot z$ where $\sin z \neq 0$). Let $Q = \{w : \operatorname{Re} w > 0,\ \operatorname{Im} w \le 0\}$ be the closed sine quadrant, $\Sigma = \{z : 0 \le \operatorname{Re} z \le \pi,\ \operatorname{Im} z \ge 0\}$ the half-strip, and $\Omega = \{z \in \Sigma : \operatorname{sinc}(z) \in Q\}$. The definition file shows that $\operatorname{sinc}$ restricts to a homeomorphism $\Omega \to Q$; let $S : \mathbb{C} \to \mathbb{C}$ be its inverse on $Q$, extended by $S(w) = 0$ for $w \notin Q$. With the reflection $\rho(s) = \operatorname{Re} s + i\,|\operatorname{Im} s|$ and the principal square root $\sqrt{\cdot}$, define
--   $$
--   \mathcal B(s) = \operatorname{ccot}\!\Big( S\big( \rho(s)^{-1/2} \big) \Big), \qquad \rho(s)^{-1/2} := \frac{1}{\sqrt{\rho(s)}} .
--   $$
--
--   **Theorem.** For every real $x > 0$ the function $\mathcal B : \mathbb{C} \to \mathbb{C}$ is continuous at the point $x$:
--   $$
--   \lim_{s \to x,\ s \in \mathbb{C}} \mathcal B(s) = \mathcal B(x).
--   $$
--
--   Thanks to the reflection $\rho$, $\mathcal B$ is defined on the whole plane and is symmetric under complex conjugation of $s$. The positive real axis is exactly where the argument $\rho(s)^{-1/2}$ reaches the boundary $\operatorname{Im} w = 0$ of $Q$, so this lemma is the statement that $\mathcal B$ has no discontinuity there; in particular, values of $\mathcal B$ on the positive axis are limits of its values in the upper half-plane.
--
--   **Formalization Note** $\mathcal B$ is `boundaryB`, $S$ is `closedSineInverse` (defined via `closedSineHomeomorph : closedSineDomain ≃ₜ closedSineQuadrant` and `0` off $Q$), $\operatorname{ccot}$ is `ccot`, $\operatorname{sinc}$ is `csinc` (`dslope Complex.sin 0`), $\rho$ is `upperReflect`, and continuity is `ContinuousAt boundaryB (x : ℂ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Functions.lean#L1252-L1267

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions

open OAI OAI.EntropyPhotonNumber
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
open Set Filter Topology

theorem OAI.EntropyPhotonNumber.continuousAt_boundaryB {x : ℝ} (hx : 0 < x) : ContinuousAt boundaryB (x : ℂ) := by sorry
