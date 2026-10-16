-- Prove2me | Theorems.Thm_OAI_EnsembleL2_mixture_operator
-- name    : OAI.EnsembleL2.mixture_operator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:27:14.569592+00:00
-- url     : https://prove2.me/theorems/a2b691b1-628e-4498-9e90-7f6b5ed49722
-- title:
--   The ensemble operator of a convex mixture of ensembles
-- statement:
--   Let $E$ be a complex Hilbert space, let $(v_i)_{i\in I}$ and $(w_j)_{j\in J}$ be families in $E$ with $\sum_i\|v_i\|^2<\infty$ and $\sum_j\|w_j\|^2<\infty$, and let $t\in[0,1]$. The *mixture* of the two families is the family indexed by the disjoint union $I\sqcup J$,
--   $$m_t(i)=\sqrt t\,v_i\quad(i\in I),\qquad m_t(j)=\sqrt{1-t}\,w_j\quad(j\in J).$$
--   For a square-summable family $u$ write $\Omega(u)=\sum_k|u_k\rangle\langle u_k|$ for its ensemble operator. Then
--   $$\Omega(m_t)=t\,\Omega(v)+(1-t)\,\Omega(w).$$
--
--   So concatenating rescaled ensembles realizes the convex combination $t\rho+(1-t)\sigma$ of the corresponding density operators; this is how a convex mixture of states is represented by a single vector ensemble in later variance computations.
--
--   **Formalization Note** $\Omega(u)$ is `TraceEnsemble.operator u`, defined as the `tsum` of the rank-one operators $|u_k\rangle\langle u_k|$ (which converges in operator norm for square-summable families).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Contraction.lean#L436-L456

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
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.EnsembleL2.mixture_operator (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) :
    TraceEnsemble.operator (mixture v w t)=
      (t:ℂ) • TraceEnsemble.operator v+((1-t:ℝ):ℂ) • TraceEnsemble.operator w := by sorry
