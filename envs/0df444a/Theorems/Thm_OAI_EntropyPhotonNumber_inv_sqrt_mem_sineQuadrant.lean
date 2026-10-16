-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_sineQuadrant
-- name    : OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:13.381118+00:00
-- url     : https://prove2.me/theorems/594ede62-fcd1-4f30-bb7c-a7aad5c44e33
-- title:
--   The reciprocal principal square root maps the open upper half-plane into the fourth quadrant
-- statement:
--   Let $\sqrt{s}=s^{1/2}=\exp(\tfrac12\operatorname{Log}s)$ denote the principal complex square root (with the principal branch of the logarithm), and let
--   $$
--   Q=\{z\in\mathbb{C}:\ \operatorname{Re}z>0,\ \operatorname{Im}z<0\}
--   $$
--   be the open fourth quadrant.
--
--   **Theorem.** For every $s\in\mathbb{C}$ with $\operatorname{Im}s>0$,
--   $$
--   \frac{1}{\sqrt{s}}\in Q,\qquad\text{i.e.}\qquad \operatorname{Re}\frac{1}{\sqrt s}>0\ \text{ and }\ \operatorname{Im}\frac{1}{\sqrt s}<0 .
--   $$
--
--   The quadrant $Q$ is the domain on which an inverse of a sine-type map is applied in the construction of auxiliary analytic functions of the upper half-plane; this lemma guarantees that $s\mapsto 1/\sqrt s$ feeds the upper half-plane into that domain.
--
--   **Formalization Note** $\sqrt{s}$ is Mathlib's `Complex.sqrt s`, defined as `s ^ (2⁻¹ : ℂ)`, and $Q$ is `sineQuadrant`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Functions.lean#L874-L892

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

theorem OAI.EntropyPhotonNumber.inv_sqrt_mem_sineQuadrant {s : ℂ} (hs : 0 < s.im) :
    (Complex.sqrt s)⁻¹ ∈ sineQuadrant := by sorry
