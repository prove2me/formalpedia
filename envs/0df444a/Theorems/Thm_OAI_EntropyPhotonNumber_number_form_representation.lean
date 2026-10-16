-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_number_form_representation
-- name    : OAI.EntropyPhotonNumber.number_form_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:02:56.666141+00:00
-- url     : https://prove2.me/theorems/f6d4f250-f0d5-4184-8583-2ffca13d5049
-- title:
--   Positive-operator representation of the regularized photon-number form
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ with number basis $|k\rangle$ and $|k|=k_1+\dots+k_n$, let $\mathcal E(y)=\sum_k|k|\,|\langle k|y\rangle|^2\in[0,\infty]$ be the photon-number (energy) form, and let $\mathcal N^{-1/2}$ be multiplication by $(1+|k|)^{-1/2}$. For every $n$ there is a positive bounded operator $B$ on $\mathcal F_n$ such that for all $x\in\mathcal F_n$
--
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\mathcal E\big(\mathcal N^{-1/2}x\big).
--   $$
--
--   Since $\mathcal E(\mathcal N^{-1/2}x)=\sum_k\frac{|k|}{1+|k|}|x(k)|^2$, $B$ plays the role of the bounded operator $\hat N(1+\hat N)^{-1}$, with $\hat N$ the total photon-number operator. It is the energy part of the regularized forms that are combined with logarithmic terms in the variational analysis.
--
--   **Formalization Note** The right-hand side is `numberVectorMoment (energyInverse n x)`, an `ENNReal` series; the conclusion is stated as `ENNReal.ofReal (Re ⟨x, B x⟩) = ...`, so both sides live in $[0,\infty]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1825-L1841

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

theorem OAI.EntropyPhotonNumber.number_form_representation (n : ℕ) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re = numberVectorMoment (energyInverse n x) := by sorry
