-- Prove2me | Theorems.Thm_OAI_QuantumTrace_gibbs_form_energy_identity
-- name    : OAI.QuantumTrace.gibbs_form_energy_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:04:20.090405+00:00
-- url     : https://prove2.me/theorems/57b0eb5f-63b1-4b97-bec5-ae166a686901
-- title:
--   Energy identity for an eigenbasis of $D A^{-1} D$: two ways of summing a weighted trace
-- statement:
--   Let $\iota$ be an index type, $H=\ell^2(\iota;\mathbb{C})$ with standard basis $(e_i)_{i\in\iota}$, and let $s:\iota\to\mathbb{R}$ satisfy $s_i\ge 1$ for all $i$. Write $D$ for the bounded diagonal operator $(Dx)_i=s_i^{-4}x_i$. Let $A$ be a strictly positive bounded operator on $H$ (positive and invertible), and let $(c_l)_{l\in L}$ be a Hilbert basis of $H$ with
--   $$
--   D A^{-1} D\, c_l = u_l^{-1}\, c_l,\qquad u_l>0 \quad(l\in L).
--   $$
--   Let $T$ be a bounded operator on $H$ with a Hilbert basis $(b_j)_{j\in J}$ of eigenvectors, $Tb_j=p_jb_j$ with $p_j\ge 0$, and assume that the family $\bigl(s_i^8\,\operatorname{Re}\langle e_i,Te_i\rangle\bigr)_{i\in\iota}$ is summable.
--
--   Then there are vectors $y_j\in H$ $(j\in J)$ such that:
--
--   1. $(y_j)_i=s_i^4\sqrt{p_j}\,(b_j)_i$ for all $i,j$, and $D y_j=\sqrt{p_j}\,b_j$;
--   2. $\sum_j\|y_j\|^2$ converges and $\displaystyle\sum_{j}\|y_j\|^2=\sum_{i}s_i^8\operatorname{Re}\langle e_i,Te_i\rangle$;
--   3. $\sum_j\operatorname{Re}\langle y_j,Ay_j\rangle$ converges, and the series on the left below converges (unconditionally) to the value on the right:
--   $$
--   \sum_{l\in L}u_l\,\operatorname{Re}\langle c_l,Tc_l\rangle=\sum_{j\in J}\operatorname{Re}\langle y_j,Ay_j\rangle .
--   $$
--
--   Formally the $u_l$ are the eigenvalues of the unbounded operator $K=D^{-1}AD^{-1}$, and $y_j=D^{-1}T^{1/2}b_j$; the identity then says that the trace of $T$ against $K$ can be computed either in the eigenbasis of $K$ or through the vectors $y_j$, where only the bounded operator $A$ appears. This is the abstract trace identity behind the energy computations for Gibbs-type states on Fock space.
--
--   **Formalization Note** Inner products are conjugate-linear in the first argument. $A^{-1}$ is `Ring.inverse A`, which is the genuine inverse because strict positivity includes invertibility. All infinite sums are unconditional sums (`HasSum`/`tsum`) over arbitrary index types.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1907-L1971

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
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
variable {ι J L : Type*}

theorem OAI.QuantumTrace.gibbs_form_energy_identity (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (A : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (hA : IsStrictlyPositive A)
    (c : HilbertBasis L ℂ (SequenceHilbert ι)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (heU : ∀ l, (inversePower s hs 4*Ring.inverse A*inversePower s hs 4) (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l)
    (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (heT : ∀ j, T (b j) = (p j : ℂ) • b j)
    (hm : Summable (fun i => s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re)) :
    ∃ y : J → SequenceHilbert ι,
      (∀ j i, y j i = (s i^4 : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) ∧
      (∀ j, inversePower s hs 4 (y j) = (Real.sqrt (p j) : ℂ) • b j) ∧
      Summable (fun j => ‖y j‖^2) ∧
      (∑' j, ‖y j‖^2) = ∑' i, s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re ∧
      Summable (fun j => (inner ℂ (y j) (A (y j))).re) ∧
      HasSum (fun l => u l*(inner ℂ (c l) (T (c l))).re)
        (∑' j, (inner ℂ (y j) (A (y j))).re) := by sorry
