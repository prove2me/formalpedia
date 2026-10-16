-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_first_dual_conditional
-- name    : OAI.EntropyPhotonNumber.first_dual_conditional
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:46:42.012898+00:00
-- url     : https://prove2.me/theorems/37900917-475a-46d4-ab19-a937c606dd59
-- title:
--   Heisenberg dual of beam-splitter mixing with a fixed second input
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space and $F\otimes F\cong\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$ the two-port space. For $\eta\in[0,1]$ let $U_\eta$ be the passive beam-splitter unitary on $F\otimes F$ (the same rotation with transmissivity $\eta$ in every mode). Fix a state $\sigma$ on $F$ and let $\Phi_\sigma$ be the channel $\rho\mapsto\operatorname{Tr}_2\bigl[U_\eta(\rho\otimes\sigma)U_\eta^*\bigr]$, with Kraus operators $V_{e,m}x=\langle e|_2\,U_\eta(x\otimes\sqrt\sigma|m\rangle)$, $e,m\in\mathbb{N}^n$ (the slice of the second port at number $e$). Its Heisenberg dual is $\Phi^*_\sigma(Z)=\sum_{e,m}V_{e,m}^*ZV_{e,m}$.
--
--   Then for every bounded operator $Z$ on $F$ and all $x,x'\in F$,
--   $$\langle x,\Phi_\sigma^*(Z)\,x'\rangle=\sum_{m\in\mathbb{N}^n}\Bigl\langle x\otimes\sqrt\sigma|m\rangle,\;U_\eta^*(Z\otimes\mathrm{Id})U_\eta\,\bigl(x'\otimes\sqrt\sigma|m\rangle\bigr)\Bigr\rangle ;$$
--   that is, $\Phi_\sigma^*(Z)$ is the partial expectation, over the second input in state $\sigma$, of the conjugated observable $U_\eta^*(Z\otimes\mathrm{Id})U_\eta$.
--
--   This identifies the dual of the "first-input" beam-splitter channel with a conditional expectation of a unitarily rotated observable, which is the form in which conditional variances of beam-splitter outputs are compared with input variances.
--
--   **Formalization Note** In Lean the statement is the operator equality `dual (firstKraus η hη σ) _ Z = conditionalLeft (rootColumn σ) _ (conjugate η hη Z)`, where `rootColumn σ m` $=\sqrt\sigma|m\rangle$, `conjugate η hη Z` $=U_\eta^*(Z\otimes\mathrm{Id})U_\eta$, and `dual` of a Kraus family is defined weakly by $\langle x,\mathrm{dual}(Z)y\rangle=\sum_i\langle V_ix,ZV_iy\rangle$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Duality.lean#L90-L104

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

open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

theorem OAI.EntropyPhotonNumber.first_dual_conditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    dual (firstKraus η hη σ) (firstKraus_norm η hη σ) Z=
      conditionalLeft (rootColumn σ) (rootColumn_norm σ) (conjugate η hη Z) := by sorry
