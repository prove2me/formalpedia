-- Prove2me | Theorems.Thm_OAI_QuantumTrace_energySet_totallyBounded
-- name    : OAI.QuantumTrace.energySet_totallyBounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:17.0952+00:00
-- url     : https://prove2.me/theorems/cfc14086-cd5f-4dc6-935e-4e99be24bc9e
-- title:
--   Density operators with energy at most $E$ form a totally bounded set
-- statement:
--   Let $H$ be a complex Hilbert space with a Hilbert (orthonormal) basis $(b_k)_{k\in\mathbb N^n}$ indexed by $\mathbb N^n$, write $|k|=k_1+\dots+k_n$, and for $E\in\mathbb R$ let $\mathcal S_E$ be the set of bounded operators $T$ on $H$ such that $T$ is positive, the series $\sum_k\operatorname{Re}\langle b_k,Tb_k\rangle$ converges to $1$, and the series $\sum_k|k|\operatorname{Re}\langle b_k,Tb_k\rangle$ converges with sum at most $E$. These are the density operators of energy at most $E$ with respect to the number grading given by the basis; operators carry the operator-norm topology. Then for every $E\in\mathbb R$,
--
--   $$
--   \mathcal S_E\ \text{is totally bounded in operator norm,}
--   $$
--
--   that is, for every $\varepsilon>0$ it is covered by finitely many operator-norm balls of radius $\varepsilon$. Combined with closedness of $\mathcal S_E$ this gives compactness of the set of density operators with bounded energy in the (complete) space of bounded operators, a quantum analogue of tightness of probability measures with bounded first moment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L740-L786

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
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.QuantumTrace.energySet_totallyBounded {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    TotallyBounded (energySet b E) := by sorry
