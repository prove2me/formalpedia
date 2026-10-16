-- Prove2me | Theorems.Thm_OAI_QuantumCalculus_matrix_duhamel_hessian
-- name    : OAI.QuantumCalculus.matrix_duhamel_hessian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:37:31.523794+00:00
-- url     : https://prove2.me/theorems/5b5d6f30-775d-48e3-80d9-9019b09c5096
-- title:
--   Duhamel second-order form of the matrix logarithm equals the logarithmic-mean quadratic form
-- statement:
--   Let $I$ be a finite index set, let $p_i>0$ for $i\in I$, and let $D=\operatorname{diag}(\log p_i)_{i\in I}$. For every Hermitian matrix $Z\in\mathbb{C}^{I\times I}$,
--   $$\operatorname{Re}\operatorname{Tr}\Bigl[\Bigl(\int_0^1 e^{(1-s)D}\,Z\,e^{sD}\,ds\Bigr)Z\Bigr]=\sum_{i\in I}\sum_{j\in I}L(p_i,p_j)\,|Z_{ij}|^2 ,$$
--   where $L(a,b)=\frac{b-a}{\log b-\log a}$ for $a\neq b$ and $L(a,a)=a$ is the logarithmic mean.
--
--   The integral $\int_0^1e^{(1-s)D}Ze^{sD}ds$ is the Duhamel (Fréchet) derivative of the matrix exponential at $D$ in direction $Z$, so the left side is the second-order term of $\operatorname{Tr}e^{D+tZ}$ at $\rho=e^{D}=\operatorname{diag}(p)$. The identity shows that this Hessian is the Bogoliubov–Kubo–Mori quadratic form $\sum_{i,j}L(p_i,p_j)|Z_{ij}|^2$.
--
--   **Formalization Note** The integral is a Bochner interval integral in the matrix space, $e^{(\cdot)}$ is `NormedSpace.exp`, and $\operatorname{Re}\operatorname{Tr}$ is the real-linear functional `matrixReTrace`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L1032-L1064

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

open OAI OAI.QuantumCalculus
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
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem OAI.QuantumCalculus.matrix_duhamel_hessian (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) :
    matrixReTrace ((∫ s in (0 : ℝ)..1,
      exp ((1-s) • Matrix.diagonal (fun i => (Real.log (p i) : ℂ))) * Z *
      exp (s • Matrix.diagonal (fun i => (Real.log (p i) : ℂ)))) * Z) =
        ∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j) := by sorry
