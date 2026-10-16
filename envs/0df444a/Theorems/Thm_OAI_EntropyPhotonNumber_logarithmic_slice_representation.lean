-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_logarithmic_slice_representation
-- name    : OAI.EntropyPhotonNumber.logarithmic_slice_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:02:17.721975+00:00
-- url     : https://prove2.me/theorems/19b1e23b-e61c-49f4-95e0-b6a41930f737
-- title:
--   Positive-operator representation of the sliced $-\log\rho$ form after energy regularization
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and $|k|=k_1+\dots+k_n$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$; its energy is $E(\rho)=\sum_k|k|\,\langle k|\rho|k\rangle$, and $\rho$ has finite energy if this series converges. For $r>0$ let $\tau_r$ be the thermal state, the diagonal operator with entries $w_r(k)=\prod_{j=1}^n\frac1{r+1}\big(\frac r{r+1}\big)^{k_j}$. Let $\rho$ be a state with $\kappa\,\tau_r\le\rho$ (operator order) for some $r>0$ and $0<\kappa\le1$, and let $(b_j)_{j\in J}$ be a Hilbert (orthonormal) eigenbasis of $\rho$, $\rho\,b_j=p_jb_j$, with $p_j>0$ and $\sum_jp_j=1$. Let $(V_i)_{i\in I}$ be bounded operators on $\mathcal F_n$ that form an isometric family, $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$, and whose energy growth is bounded: with $\mathcal E(y)=\sum_k|k|\,|\langle k|y\rangle|^2\in[0,\infty]$ there is $F\ge0$ such that
--   $$\sum_i\mathcal E(V_ix)\le\mathcal E(x)+F\,\|x\|^2\quad\text{in }[0,\infty]\quad\text{for all }x .$$
--   Let $\mathcal N^{-1/2}$ be multiplication by $(1+|k|)^{-1/2}$. Then there is a positive bounded operator $B$ on $\mathcal F_n$ such that for every $x$
--
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\sum_{i\in I}\sum_{j\in J}(-\log p_j)\,\big|\langle b_j,\,V_i\mathcal N^{-1/2}x\rangle\big|^2 .
--   $$
--
--   Formally $B=\mathcal N^{-1/2}\big(\sum_iV_i^*(-\log\rho)V_i\big)\mathcal N^{-1/2}$: the Heisenberg-picture image of $-\log\rho$ under the channel with Kraus operators $V_i$, sandwiched by $\mathcal N^{-1/2}$, is a genuine bounded positive operator. Such bounded representatives of logarithms are what makes trace identities involving $\log\rho$ under beam-splitter channels rigorous on the full Fock space.
--
--   **Formalization Note** The right-hand side is `sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) V (energyInverse n x)`, an `ENNReal` series, and the conclusion reads `ENNReal.ofReal (Re ⟨x, B x⟩) = ...`; the energy moments are `vectorMoment (fun k => totalNumber k)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L1779-L1819

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
open QuantumTrace TensorLp

theorem OAI.EntropyPhotonNumber.logarithmic_slice_representation {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J I : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (V : I → Fock n →L[ℂ] Fock n) (F : ℝ) (hF : 0 ≤ F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hE : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+ENNReal.ofReal F*ENNReal.ofReal (‖x‖^2)) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) V (energyInverse n x) := by sorry
