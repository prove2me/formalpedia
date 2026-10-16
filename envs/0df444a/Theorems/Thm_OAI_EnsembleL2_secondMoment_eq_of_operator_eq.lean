-- Prove2me | Theorems.Thm_OAI_EnsembleL2_secondMoment_eq_of_operator_eq
-- name    : OAI.EnsembleL2.secondMoment_eq_of_operator_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:26:00.782828+00:00
-- url     : https://prove2.me/theorems/14b4e472-6bba-4ab7-96ae-72e184fe9329
-- title:
--   Ensemble second moments depend only on the ensemble operator
-- statement:
--   Let $E$ be a complex Hilbert space admitting a Hilbert basis $(b_k)_{k\in K}$. Let $(v_i)_{i\in I}$ and $(w_j)_{j\in J}$ be families in $E$ with $\sum_i\|v_i\|^2<\infty$ and $\sum_j\|w_j\|^2<\infty$, and suppose they define the same positive trace-class operator:
--   $$\sum_{i\in I}|v_i\rangle\langle v_i|=\sum_{j\in J}|w_j\rangle\langle w_j| .$$
--   Then for every bounded operator $Z$ on $E$
--   $$\sum_{i\in I}\|Zv_i\|^2=\sum_{j\in J}\|Zw_j\|^2 .$$
--
--   Thus the second moment $\sum_i\|Zv_i\|^2$ of an ensemble decomposition of a density operator $\rho$ is an invariant of $\rho$ (it equals $\operatorname{Tr}\rho Z^*Z$), so it may be computed in any convenient decomposition, for instance a spectral one or one coming from a channel.
--
--   **Formalization Note** The Hilbert basis $b$ is an explicit argument; it is used only to compute traces. The operator $\sum_i|v_i\rangle\langle v_i|$ is `TraceEnsemble.operator v`, an operator-norm convergent `tsum`, and the second moment is the `tsum` `EnsembleL2.secondMoment v Z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Contraction.lean#L203-L219

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

open OAI OAI.EnsembleL2
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
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.EnsembleL2.secondMoment_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    secondMoment v Z=secondMoment w Z := by sorry
