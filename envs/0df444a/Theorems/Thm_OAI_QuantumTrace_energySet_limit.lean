-- Prove2me | Theorems.Thm_OAI_QuantumTrace_energySet_limit
-- name    : OAI.QuantumTrace.energySet_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:52:31.822986+00:00
-- url     : https://prove2.me/theorems/a09c9f38-c143-444d-b3d1-91f2db09b71f
-- title:
--   Density operators with energy at most $E$ form a closed set
-- statement:
--   Let $H$ be a complex Hilbert space with a Hilbert (orthonormal) basis $(b_k)_{k\in\mathbb N^n}$ indexed by $\mathbb N^n$, write $|k|=k_1+\dots+k_n$, and for $E\in\mathbb R$ let $\mathcal S_E$ be the set of bounded operators $T$ on $H$ such that $T$ is positive, the series $\sum_k\operatorname{Re}\langle b_k,Tb_k\rangle$ converges to $1$, and the series $\sum_k|k|\operatorname{Re}\langle b_k,Tb_k\rangle$ converges with sum at most $E$. These are the density operators of energy at most $E$ with respect to the number grading given by the basis; operators carry the operator-norm topology. Let $l$ be a nontrivial filter on a type $\alpha$, and let $T:\alpha\to B(H)$ with $T_a\in\mathcal S_E$ for every $a$ and $T_a\to A$ in operator norm along $l$. Then
--
--   $$
--   A\in\mathcal S_E .
--   $$
--
--   So $\mathcal S_E$ is closed under norm limits: positivity, the trace normalization (no mass escapes to infinity) and the energy bound all survive. The energy bound is what prevents the loss of trace in the limit. Together with total boundedness this yields compactness of the energy-bounded density operators, the basis of the existence of minimizers in the regularized entropy problem.
--
--   **Formalization Note** The limit is along a filter with `[NeBot l]`; the set is `energySet b E` and the real parts are taken because the inner products are a priori complex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L606-L655

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
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.QuantumTrace.energySet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {E : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ energySet b E) (hlim : Tendsto T l (𝓝 A)) : A ∈ energySet b E := by sorry
