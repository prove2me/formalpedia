-- Prove2me | Theorems.Thm_OAI_QuantumTrace_double_compression_norm_le
-- name    : OAI.QuantumTrace.double_compression_norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:50:35.512571+00:00
-- url     : https://prove2.me/theorems/9438cefe-aeb9-4129-b538-9b297b05e7ac
-- title:
--   Norm bound for compressing a density operator to finitely many basis vectors
-- statement:
--   Let $H$ be a complex Hilbert space with a Hilbert (orthonormal) basis $(b_i)_{i\in\iota}$, and let $T$ be a positive bounded operator on $H$ whose diagonal sums to $1$, i.e. $\sum_i\operatorname{Re}\langle b_i,Tb_i\rangle=1$ (convergent series). For a finite set $s\subseteq\iota$ let $P_s$ be the orthogonal projection onto the span of $\{b_i:i\in s\}$. Then
--
--   $$
--   \big\|T-P_s\,T\,P_s\big\|\le2\sqrt{1-\sum_{i\in s}\operatorname{Re}\langle b_i,Tb_i\rangle}\,,
--   $$
--
--   where $\|\cdot\|$ is the operator norm. In words: if a density operator puts all but a mass $m$ of its trace on finitely many basis vectors, then its compression to those vectors is within $2\sqrt m$ of it in operator norm. Combined with a tail bound such as Markov's inequality for the photon number, this gives uniform finite-dimensional approximation of energy-bounded density operators.
--
--   **Formalization Note** $P_s$ is `basisProjection b s`, defined as $\sum_{i\in s}|b_i\rangle\langle b_i|$; compositions are written with `∘L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L537-L578

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

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

theorem OAI.QuantumTrace.double_compression_norm_le (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hp : T.IsPositive) (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) 1)
    (s : Finset ι) :
    ‖T - basisProjection b s ∘L T ∘L basisProjection b s‖ ≤
      2 * Real.sqrt (1 - ∑ i ∈ s, (inner ℂ (b i) (T (b i))).re) := by sorry
