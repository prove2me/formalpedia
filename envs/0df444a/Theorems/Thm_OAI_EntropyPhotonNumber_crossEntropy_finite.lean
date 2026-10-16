-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_crossEntropy_finite
-- name    : OAI.EntropyPhotonNumber.crossEntropy_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:08:15.657438+00:00
-- url     : https://prove2.me/theorems/5397aba3-4142-4e47-9730-63c0efbeb72b
-- title:
--   Finite cross entropy against a state that dominates a multiple of a thermal state
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$. The energy of $\sigma$ is $E(\sigma)=\sum_k|k|\,\langle k|\sigma|k\rangle$, and $\sigma$ has finite energy if this series converges. For $r>0$, the thermal state $\tau_r$ is diagonal in the number basis with
--   $$
--   \langle k|\tau_r|k\rangle=\prod_{m=1}^n\frac{1}{r+1}\Bigl(\frac{r}{r+1}\Bigr)^{k_m}.
--   $$
--
--   Let $\rho,\sigma$ be states on $\mathcal F_n$ with $\sigma$ of finite energy. Let $r>0$ and $0<\kappa\le1$, and assume $\kappa\,\tau_r\le\rho$ in the operator order, i.e. $\rho-\kappa\tau_r$ is positive. Let $(b_j)_{j\in J}$ be a Hilbert basis of eigenvectors of $\rho$, $\rho b_j=p_jb_j$, with $p_j>0$ for all $j$ and $\sum_jp_j=1$. Then the series
--   $$
--   \sum_{j\in J}(-\log p_j)\,\operatorname{Re}\langle b_j,\sigma b_j\rangle
--   $$
--   converges. In other words, the cross entropy $-\operatorname{Tr}\sigma\log\rho$ is finite.
--
--   A lower bound $\rho\ge\kappa\tau_r$ controls $-\log\rho$ by a constant plus a multiple of the number operator. This makes the cross entropy of any finite-energy state against $\rho$ finite, which is the regularity needed before applying Klein's inequality to such states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L339-L358

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

theorem OAI.EntropyPhotonNumber.crossEntropy_finite {n : ℕ} (ρ σ : State n) (hσ : FiniteEnergy σ)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re) := by sorry
