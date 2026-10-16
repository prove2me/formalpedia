-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_spectralLogData_of_sandwich
-- name    : OAI.EntropyPhotonNumber.spectralLogData_of_sandwich
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:37.229764+00:00
-- url     : https://prove2.me/theorems/73eed78d-0753-44d5-8d75-0b211b2f6e22
-- title:
--   Building spectral logarithm data from a positive log-sandwich operator
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)$, $|k|=k_1+\dots+k_n$, annihilation operators $a_j$, $\hat n_j=a_j^\dagger a_j$, and the diagonal weight $\hat N=1+\sum_j\hat n_j$ (so $\hat N|k\rangle=(1+|k|)|k\rangle$). States are positive operators on $F$ with number-basis diagonal summing to $1$; $E(\rho)=\sum_k|k|\rho_{kk}$, and $\rho$ has finite $m$-th moment if $\sum_k(1+|k|)^m\rho_{kk}<\infty$. For $r>0$, $\tau_r$ denotes the thermal state with mean photon number $r$ per mode, $\langle k|\tau_r|l\rangle=\delta_{kl}\prod_i\frac1{r+1}(\frac r{r+1})^{k_i}$, and $h(r)=\log(r+1)-\log r$.
--
--   A *spectral logarithm datum* for a state $\rho$ consists of a Hilbert basis $(b_j)_{j\in J}$ of $F$ and $p_j>0$ with $\sum_jp_j=1$ and $\rho b_j=p_jb_j$; spectral columns $x_j\in F$ with $\sum_j\|x_j\|^2<\infty$ and $\hat N^{-3}x_j=\sqrt{p_j}\,b_j$; and a bounded symmetric operator $\mathcal L$ (the log sandwich) with
--   $$\operatorname{Re}\langle y,\mathcal Ly\rangle=\sum_j(-\log p_j)\,\bigl|\langle b_j,\hat N^{-2}y\rangle\bigr|^2\quad(y\in F),\qquad \mathcal L(\hat N^{-1}x_j)=(-\log p_j)\,\hat N^{-5}x_j .$$
--   Formally $\mathcal L=\hat N^{-2}(-\log\rho)\hat N^{-2}$.
--
--   **Theorem.** Let $\rho$ be a state with finite sixth moment, let $(b_j)_{j\in J}$ be a Hilbert basis of $F$ and $p_j>0$ with $\sum_jp_j=1$ and $\rho b_j=p_jb_j$ for all $j$. Let $B$ be a positive bounded operator on $F$ such that for all $x\in F$, in $[0,\infty]$,
--   $$\langle x,Bx\rangle=\sum_{j\in J}(-\log p_j)\,\bigl|\langle b_j,\hat N^{-2}x\rangle\bigr|^2 .$$
--   Then there is a spectral logarithm datum for $\rho$ whose index set is $J$, whose basis is $(b_j)$, whose probabilities are $(p_j)$ and whose log sandwich is $B$.
--
--   Thus a positive operator that represents the quadratic form of $\hat N^{-2}(-\log\rho)\hat N^{-2}$ automatically has all the properties required of a log sandwich, and spectral columns exist once $\rho$ has a finite sixth moment.
--
--   **Formalization Note** The datum is the structure `SpectralLogData n ρ`; since its index type is a field, the conclusion states `G.J = J` together with `HEq` for the basis and the probabilities. The form identity is an equality in `ℝ≥0∞` (`basisMoment`), with $\hat N^{-2}$ = `inverseWeight 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L783-L848

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

theorem OAI.EntropyPhotonNumber.spectralLogData_of_sandwich (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j) (hm : FiniteMoment 6 ρ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) :
    ∃ G : SpectralLogData n ρ, G.J=J ∧ HEq G.basis b ∧ HEq G.probability p ∧ G.logSandwich=B := by sorry
