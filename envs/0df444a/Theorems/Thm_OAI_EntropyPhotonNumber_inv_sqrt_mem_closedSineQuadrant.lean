-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_closedSineQuadrant
-- name    : OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:41.900979+00:00
-- url     : https://prove2.me/theorems/3c19a132-ad71-4b9f-93a2-f46f3e980a11
-- title:
--   Reciprocal square roots of right half-plane points on or above the real axis lie in the closed lower-right quadrant
-- statement:
--   For $s \in \mathbb{C}$ let $\sqrt{s} = s^{1/2} = \exp(\tfrac12 \operatorname{Log} s)$ be the principal square root, and let
--   $$
--   Q = \{\, w \in \mathbb{C} : \operatorname{Re} w > 0,\ \operatorname{Im} w \le 0 \,\}
--   $$
--   be the *closed sine quadrant* (closed along the positive real axis, open along the imaginary axis).
--
--   **Theorem.** If $s \in \mathbb{C}$ satisfies $\operatorname{Re} s > 0$ and $\operatorname{Im} s \ge 0$, then
--   $$
--   \frac{1}{\sqrt{s}} \in Q, \qquad\text{that is,}\qquad \operatorname{Re}\frac{1}{\sqrt{s}} > 0 \quad\text{and}\quad \operatorname{Im}\frac{1}{\sqrt{s}} \le 0 .
--   $$
--
--   The set $Q$ is the target of the closed-quadrant inverse of the complex sinc function $z \mapsto \sin z / z$ that enters the boundary function used for the photon-number functions. The lemma guarantees that the argument $s^{-1/2}$ fed to that inverse lies in $Q$ for every $s$ in the right half-plane on or above the real axis, including the positive real axis itself.
--
--   **Formalization Note** $\sqrt{s}$ is Mathlib's `Complex.sqrt s = s ^ (2⁻¹ : ℂ)` and $Q$ is `closedSineQuadrant`; the reciprocal is the field inverse `⁻¹`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Functions.lean#L1208-L1221

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

theorem OAI.EntropyPhotonNumber.inv_sqrt_mem_closedSineQuadrant {s : ℂ} (hr : 0 < s.re) (hi : 0 ≤ s.im) :
    (Complex.sqrt s)⁻¹ ∈ closedSineQuadrant := by sorry
