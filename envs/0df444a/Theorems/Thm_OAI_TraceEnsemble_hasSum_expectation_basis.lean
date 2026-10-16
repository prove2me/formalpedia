-- Prove2me | Theorems.Thm_OAI_TraceEnsemble_hasSum_expectation_basis
-- name    : OAI.TraceEnsemble.hasSum_expectation_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:29:31.180185+00:00
-- url     : https://prove2.me/theorems/3dda1fad-26c5-4d9c-9573-cff666ade7ca
-- title:
--   Basis trace of $Z\rho$ for a density operator given by a vector ensemble
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert basis $(b_j)_{j\in J}$, and let $(v_i)_{i\in I}$ be a family in $E$ with $\sum_i\|v_i\|^2<\infty$. Put $\rho_v=\sum_i|v_i\rangle\langle v_i|$, a positive trace-class operator. Then for every bounded operator $Z$ on $E$ the series below converges unconditionally and
--   $$\sum_{j\in J}\bigl\langle b_j,\;Z\rho_v\,b_j\bigr\rangle=\sum_{i\in I}\langle v_i,\,Zv_i\rangle .$$
--
--   In words, the trace of $Z\rho_v$ computed in an arbitrary orthonormal basis equals the ensemble expectation of $Z$. This is what allows expectations $\operatorname{Tr}\rho Z$ to be evaluated in whichever basis is convenient, e.g. the eigenbasis of a reference state.
--
--   **Formalization Note** The left side is stated as `HasSum` over $J$ with value `expectation v Z` $=\sum_i\langle v_i,Zv_i\rangle$ (a `tsum`); $\rho_v$ is `operator v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L341-L358

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

open OAI OAI.TraceEnsemble
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem OAI.TraceEnsemble.hasSum_expectation_basis (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator v (b j)))) (expectation v Z) := by sorry
