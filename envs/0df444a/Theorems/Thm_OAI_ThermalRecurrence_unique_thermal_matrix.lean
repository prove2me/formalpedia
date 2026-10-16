-- Prove2me | Theorems.Thm_OAI_ThermalRecurrence_unique_thermal_matrix
-- name    : OAI.ThermalRecurrence.unique_thermal_matrix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T03:02:19.48627+00:00
-- url     : https://prove2.me/theorems/ad1a6fa1-e363-4ef2-822a-96dc8b575a31
-- title:
--   The thermal balance recurrence has the thermal matrix as its only normalized Hermitian solution
-- statement:
--   Let $n\in\mathbb{N}$ and $r>0$, and let $M:\mathbb{N}^n\times\mathbb{N}^n\to\mathbb{C}$ be a matrix indexed by multi-indices. For $p\in\mathbb{N}^n$ and a mode $j$ write $p-e_j$ for $p$ with its $j$-th entry decreased by one (truncated at $0$). Suppose:
--
--   1. (*thermal balance*) for every mode $j$ and all $p,b\in\mathbb{N}^n$ with $p_j>0$,
--   $$(r+1)\sqrt{p_j}\;M(p,b)=r\sqrt{b_j}\;M(p-e_j,\,b-e_j);$$
--   2. (*Hermitian*) $M(b,p)=\overline{M(p,b)}$ for all $p,b$;
--   3. (*normalized*) $\sum_{p}\operatorname{Re}M(p,p)=1$ (a convergent series).
--
--   Then for all $p,b\in\mathbb{N}^n$
--   $$M(p,b)=\begin{cases}\displaystyle\prod_{j=1}^n\frac1{r+1}\Bigl(\frac r{r+1}\Bigr)^{p_j},&p=b,\\ 0,&p\neq b.\end{cases}$$
--
--   Condition 1 is the number-basis form of the operator identity $(r+1)\,a_jM=r\,Ma_j$ for every mode. The theorem says that the $n$-mode thermal state with mean photon number $r$ per mode is the unique normalized Hermitian matrix satisfying this balance, which is how vanishing defects identify limiting states as thermal.
--
--   **Formalization Note** The balance is `ThermalRecurrence.Balance r M`, where `lower p j` subtracts one in natural numbers; when $b_j=0$ the right side carries the factor $\sqrt0=0$, so the truncation is harmless. The value on the diagonal is `QuantumTrace.thermalWeight n r p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean#L239-L278

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
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalLimit

open OAI OAI.ThermalRecurrence
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

theorem OAI.ThermalRecurrence.unique_thermal_matrix (n : ℕ) {r : ℝ} (hr : 0 < r)
    {M : (Fin n → ℕ) → (Fin n → ℕ) → ℂ} (hM : Balance r M)
    (hstar : ∀ p b, M b p = conj (M p b))
    (htrace : HasSum (fun p => (M p p).re) 1) (p b : Fin n → ℕ) :
    M p b = if p = b then (QuantumTrace.thermalWeight n r p : ℂ) else 0 := by sorry
