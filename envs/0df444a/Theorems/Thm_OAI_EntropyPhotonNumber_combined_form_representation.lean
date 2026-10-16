-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_combined_form_representation
-- name    : OAI.EntropyPhotonNumber.combined_form_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:03:32.011212+00:00
-- url     : https://prove2.me/theorems/45c9005b-07a9-40fc-be02-d4048826f95c
-- title:
--   Nonnegative combinations of represented regularized forms are represented
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$, $|k|=k_1+\dots+k_n$, let $\mathcal N^{-1/2}$ be multiplication by $(1+|k|)^{-1/2}$ and $\mathcal E(y)=\sum_k|k|\,|\langle k|y\rangle|^2\in[0,\infty]$. Let $(b_j)_{j\in J}$ be a Hilbert (orthonormal) basis of $\mathcal F_n$, $w:J\to[0,\infty]$ a weight, $(V_i)_{i\in I}$ bounded operators, and
--   $$\Theta(y)=\sum_{i\in I}\sum_{j\in J}w_j\,|\langle b_j,V_iy\rangle|^2\in[0,\infty].$$
--   Suppose $B$ is a positive bounded operator with $\operatorname{Re}\langle x,Bx\rangle=\Theta(\mathcal N^{-1/2}x)$ for all $x$, and let $\alpha,\beta\ge0$. Then there is a positive bounded operator $C$ such that for all $x$
--
--   $$
--   \operatorname{Re}\langle x,Cx\rangle=\alpha\,\Theta\big(\mathcal N^{-1/2}x\big)+\beta\,\mathcal E\big(\mathcal N^{-1/2}x\big).
--   $$
--
--   So a represented sliced form (for instance the regularized $-\log\rho$ form) can be combined with the regularized photon-number form with nonnegative coefficients, and the result is again represented by a bounded positive operator. This packages the "entropy plus energy" combinations appearing in the variational problem.
--
--   **Formalization Note** All equalities are between `ENNReal` values: the hypothesis and conclusion are stated as `ENNReal.ofReal (Re ⟨x, B x⟩) = sliceMoment b w V (energyInverse n x)` and with $\alpha,\beta$ embedded by `ENNReal.ofReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1843-L1863

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

open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open QuantumTrace

theorem OAI.EntropyPhotonNumber.combined_form_representation {n : ℕ} {J I : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞) (V : I → Fock n →L[ℂ] Fock n)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive)
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re = sliceMoment b w V (energyInverse n x))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ C : Fock n →L[ℂ] Fock n, C.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (C x)).re =
        ENNReal.ofReal α*sliceMoment b w V (energyInverse n x)+
        ENNReal.ofReal β*numberVectorMoment (energyInverse n x) := by sorry
