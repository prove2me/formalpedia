-- Prove2me | Theorems.Thm_OAI_QuantumTrace_StochasticOverlap_hasSum_row_product
-- name    : OAI.QuantumTrace.StochasticOverlap.hasSum_row_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:05:34.022111+00:00
-- url     : https://prove2.me/theorems/54f37643-9853-42c5-b9c3-de7161543350
-- title:
--   Summing $a_{ij}p_i$ over a doubly stochastic array preserves the sum of $p$
-- statement:
--   Let $I,J$ be index sets and let $a=(a_{ij})_{i\in I,\,j\in J}$ be a real array with $a_{ij}\ge0$, every row summing to one and every column summing to one:
--   $$
--   \sum_{j\in J}a_{ij}=1\ (i\in I),\qquad \sum_{i\in I}a_{ij}=1\ (j\in J).
--   $$
--   If $p:I\to\mathbb{R}$ is a real family whose sum converges (unconditionally) to $s$, then the family $(a_{ij}\,p_i)_{(i,j)\in I\times J}$ also converges (unconditionally) to $s$:
--   $$
--   \sum_{(i,j)\in I\times J}a_{ij}\,p_i=s .
--   $$
--
--   In the development such arrays arise as overlap matrices $a_{ij}=|\langle c_j,b_i\rangle|^2$ of two Hilbert bases. This lemma is the bookkeeping step that lets one distribute a convergent series over such an overlap matrix, for example in the proof of Klein's inequality. Only the row condition is used.
--
--   **Formalization Note** The array is a `StochasticOverlap I J`, which also carries the column condition. Unconditional convergence is `HasSum`; for real families it is equivalent to absolute convergence, and $p$ may take both signs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L50-L64

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational

open OAI OAI.QuantumTrace OAI.QuantumTrace.StochasticOverlap
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped BigOperators
open Filter Topology
variable {I J : Type*} (a : StochasticOverlap I J)

theorem OAI.QuantumTrace.StochasticOverlap.hasSum_row_product (p : I → ℝ) {s : ℝ} (hp : HasSum p s) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * p ij.1) s := by sorry
