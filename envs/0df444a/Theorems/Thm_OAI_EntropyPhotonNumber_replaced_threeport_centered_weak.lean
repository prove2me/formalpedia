-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_replaced_threeport_centered_weak
-- name    : OAI.EntropyPhotonNumber.replaced_threeport_centered_weak
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:29.370229+00:00
-- url     : https://prove2.me/theorems/d7215374-98f6-47f1-9515-327111843280
-- title:
--   Centered weak generator identity for a thermally replaced two-stage beam-splitter cascade
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode bosonic Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and write $|k|=k_1+\dots+k_n$ for the total photon number. Let $\mathcal N$ denote multiplication by $1+|k|$ (so every $\mathcal N^{-m}$, $m\ge 0$, is a bounded operator), and let $a_j$ be the annihilation operator of mode $j$, $(a_jx)(k)=\sqrt{k_j+1}\,x(k+\mathbf 1_j)$, where $\mathbf 1_j$ is the $j$-th unit index; the operators $a_j\mathcal N^{-3}$ and $a_j^\dagger\mathcal N^{-3}$ are bounded. Inner products are conjugate-linear in the first slot. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$.
--
--   A *weighted column decomposition* $X$ of a state $\rho$ is a family $(x_i)_{i\in I}$ of vectors of $\mathcal F_n$ with $\sum_i\|x_i\|^2<\infty$, $\sum_i\|\mathcal N^{-3}x_i\|^2=1$ and $\rho=\sum_i|\mathcal N^{-3}x_i\rangle\langle\mathcal N^{-3}x_i|$. For such $X$, a real number $r$, a mode $j$ and a bounded operator $Z$ put
--   $$
--   \Lambda_{r,j}(X;Z)=(r+1)\sum_i\big\langle a_j\mathcal N^{-3}x_i,\;Z\,\mathcal N^{-3}x_i\big\rangle-r\sum_i\big\langle\mathcal N^{-3}x_i,\;Z\,a_j^\dagger\mathcal N^{-3}x_i\big\rangle .
--   $$ Further let $E_X(Z)=\sum_i\langle\mathcal N^{-3}x_i,Z\,\mathcal N^{-3}x_i\rangle$ be the expectation of $Z$ (it equals $\operatorname{Tr}\rho Z$), let $\mu_{r,j}(X)=\Lambda_{r,j}(X;1)$ be the weak mean, and define the centered pairing $\Lambda^\circ_{r,j}(X;Z)=\Lambda_{r,j}(X;Z)-\mu_{r,j}(X)\,E_X(Z)$.
--
--   For $\eta\in[0,1]$ let $U_\eta$ be the passive beam-splitter unitary on $\mathcal F_n\otimes\mathcal F_n=\ell^2(\mathbb N^n\times\mathbb N^n)$ that applies the same rotation with entries $\sqrt\eta,\pm\sqrt{1-\eta}$ to every pair of modes. For a decomposition $Y=(y_i)$ of $\sigma$, with $\psi_i=\mathcal N^{-3}y_i$, the *left slice* $\Phi^Y_\eta(Z)$ is the bounded operator with $\langle u,\Phi^Y_\eta(Z)v\rangle=\sum_i\langle u\otimes\psi_i,\,U_\eta^*(Z\otimes 1)U_\eta(v\otimes\psi_i)\rangle$ (the input state sits in the second port), and for $X=(x_i)$, with $\varphi_i=\mathcal N^{-3}x_i$, the *right slice* $\widetilde\Phi^X_\eta(Z)$ is defined by $\langle u,\widetilde\Phi^X_\eta(Z)v\rangle=\sum_i\langle\varphi_i\otimes u,\,U_\eta^*(Z\otimes1)U_\eta(\varphi_i\otimes v)\rangle$ (the input state sits in the first port). We write $\tau=\mathrm{BS}_\eta(\rho,\sigma)$ if every number-basis entry of $\tau$ is the sum of the convergent series defining the corresponding entry of the first-port reduced block of $U_\eta(\rho\otimes\sigma)U_\eta^*$. For $s>0$ the thermal state with parameter $s$ is diagonal with entries $w_s(k)=\prod_{j=1}^n\frac{1}{s+1}\big(\frac{s}{s+1}\big)^{k_j}$.
--
--   Let $\eta,\theta\in[0,1]$ and $\kappa,a,b,d\in\mathbb R$, let $\rho,\sigma,\tau_D,m,\gamma,\omega,\rho_0$ be states with $m=\mathrm{BS}_\eta(\rho,\sigma)$ and $\gamma=\mathrm{BS}_\theta(m,\tau_D)$, and let $X,Y,D,M,G,O,R$ be weighted column decompositions of $\rho,\sigma,\tau_D,m,\gamma,\omega,\rho_0$ respectively. Put $s=\theta(\eta a+(1-\eta)b)+(1-\theta)d$ and assume $d>0$, $s>0$, that $\tau_D$ has number-basis entries $\langle k|\tau_D|l\rangle=\delta_{kl}w_d(k)$, that $\omega$ has entries $\langle k|\omega|l\rangle=\delta_{kl}w_s(k)$, and that $\rho_0=(1-\kappa)\gamma+\kappa\,\omega$. Fix a mode $j$ and a bounded operator $Z$, and write $Z_1=\Phi^Y_\eta\big(\Phi^D_\theta(Z)\big)$ and $Z_2=\widetilde\Phi^X_\eta\big(\Phi^D_\theta(Z)\big)$. Then
--
--   $$
--   \Lambda^\circ_{s,j}(R;Z)=(1-\kappa)\Big(\sqrt\theta\sqrt\eta\;\Lambda^\circ_{a,j}(X;Z_1)+\sqrt\theta\sqrt{1-\eta}\;\Lambda^\circ_{b,j}(Y;Z_2)\Big)+\kappa(1-\kappa)\,\mu_{s,j}(G)\,\big(E_G(Z)-E_O(Z)\big).
--   $$
--
--   This is the centered form of the three-port identity: subtracting the mean part $\mu\,E(Z)$ from each pairing leaves the same two input contributions, up to an explicit correction proportional to $\kappa(1-\kappa)$ that measures how differently the unreplaced output $\gamma$ and the thermal state $\omega$ see the observable $Z$. Centered pairings are the quantities that enter quadratic (variance-type) estimates in the entropy photon-number argument.
--
--   **Formalization Note** As in the uncentered identity, $a$, $b$, $\kappa$ are arbitrary reals and the only sign conditions are $d>0$ and $s>0$. The expectation, weak mean and centered pairing are `WeightedColumns.expectation`, `weakMean` and `centeredWeak`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L671-L714

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
open QuantumTrace Annihilation BeamLadder TensorLp

theorem OAI.EntropyPhotonNumber.replaced_threeport_centered_weak
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (R : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    R.centeredWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j Z=
      ((1-κ:ℝ):ℂ)*((Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*
        X.centeredWeak a j (Y.rawSlice η hη (D.rawSlice θ hθ Z))+
        (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*
        Y.centeredWeak b j (X.rawSliceRight η hη (D.rawSlice θ hθ Z)))+
      (κ:ℂ)*((1-κ:ℝ):ℂ)*G.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j*
        (G.expectation Z-O.expectation Z) := by sorry
