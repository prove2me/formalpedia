-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_spectral_weighted_columns
-- name    : OAI.EntropyPhotonNumber.spectral_weighted_columns
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:38.483988+00:00
-- url     : https://prove2.me/theorems/4a5978ec-9937-41ae-ba5f-579afbe19db3
-- title:
--   Weighted spectral columns of a state with finite sixth moment
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$, $|k|=k_1+\dots+k_n$, and let $\mathcal N$ be multiplication by $1+|k|$. Let $\rho$ be a state on $\mathcal F_n$ (a positive bounded operator whose number-basis diagonal sums to $1$) with finite sixth moment, $\sum_k(1+|k|)^6\langle k|\rho|k\rangle<\infty$. Let $(b_j)_{j\in J}$ be a Hilbert (orthonormal) basis of $\mathcal F_n$ and $p:J\to\mathbb R$ with $p_j\ge0$ and $\rho\,b_j=p_j\,b_j$ for all $j$. Then there is a family $(x_j)_{j\in J}$ in $\mathcal F_n$ with $\sum_j\|x_j\|^2<\infty$ and
--
--   $$
--   \mathcal N^{-3}x_j=\sqrt{p_j}\;b_j\qquad\text{for every }j\in J .
--   $$
--
--   Thus the eigen-ensemble $(\sqrt{p_j}\,b_j)_j$ of $\rho$ can be written as $\mathcal N^{-3}$ applied to a square-summable family: the vectors $\mathcal N^3\sqrt{p_j}\,b_j$ exist in Fock space and have summable squared norms. This is what allows the spectral decomposition of $\rho$ to be used as a weighted column decomposition with three powers of $\mathcal N$ to spare.
--
--   **Formalization Note** $\mathcal N^{-3}$ is `inverseWeight 3`, the eigen-ensemble vector $\sqrt{p_j}\,b_j$ is `CrossEnsemble.eigenEnsemble b p j`, and the moment hypothesis is `FiniteMoment 6 ρ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean#L336-L357

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
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

theorem OAI.EntropyPhotonNumber.spectral_weighted_columns (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0≤p j) (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j)
    (hm : FiniteMoment 6 ρ) :
    ∃ x : J → Fock n, Summable (fun j => ‖x j‖^2) ∧
      ∀ j, inverseWeight 3 (x j)=CrossEnsemble.eigenEnsemble b p j := by sorry
