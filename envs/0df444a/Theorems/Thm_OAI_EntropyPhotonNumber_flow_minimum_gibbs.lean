-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_flow_minimum_gibbs
-- name    : OAI.EntropyPhotonNumber.flow_minimum_gibbs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:11:20.445065+00:00
-- url     : https://prove2.me/theorems/b612b7c5-41ab-45c2-9666-e8abcfd9e95d
-- title:
--   Minimizers of the one-port entropy functional are faithful Gibbs states of a sliced Hamiltonian
-- statement:
--   Throughout, $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, and $|k|=k_1+\dots+k_n$ is the total photon number of $k$. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k\langle k|\rho|k\rangle=1$.
--
--   **Notation.**
--   - $S(\rho)=-\operatorname{Tr}\rho\log\rho$ is the von Neumann entropy.
--   - $E(\rho)=\sum_k|k|\langle k|\rho|k\rangle$ is the energy (finite energy means this series converges).
--   - $M_m(\rho)=\sum_k(1+|k|)^m\langle k|\rho|k\rangle$ is the $m$-th number moment (finite $m$-th moment means this series converges).
--   - $N(x)=\sum_k|k|\,|x_k|^2\in[0,\infty]$ for vectors $x$, and $W_m|k\rangle=(1+|k|)^{-m/2}|k\rangle$.
--   - $\tau_r$ is the thermal state with $\langle k|\tau_r|k\rangle=\prod_m(r+1)^{-1}(r/(r+1))^{k_m}$.
--
--   A **Kraus flow** $\mathcal F$ consists of:
--   - bounded operators $(V_i)_{i\in I}$ with $\sum_i\|V_ix\|^2=\|x\|^2$ for all $x$;
--   - a constant $F_0\ge0$ with $\sum_iN(V_ix)\le N(x)+F_0\|x\|^2$ for all $x$;
--   - a map $\Phi$ from states to states such that $\Phi(\rho)=\sum_{(i,j)}|V_iv_j\rangle\langle V_iv_j|$ whenever $\rho=\sum_j|v_j\rangle\langle v_j|$ with $\sum_j\|v_j\|^2=1$, and such that $\Phi$ maps finite-energy states to finite-energy states.
--
--   **Hypotheses.**
--   - $\mathcal F$ is a Kraus flow, $r>0$ and $\tau=\tau_r$.
--   - $0<\kappa\le1$, $c>0$, $a>0$, $\beta\ge0$ and $\zeta>0$.
--   - $\rho$ is a state with finite fourth moment, and $\rho_0=(1-\kappa)\Phi(\rho)+\kappa\tau$ has an eigenbasis $(b_j)_{j\in J}$ with $\rho_0b_j=p_jb_j$, $p_j>0$, $\sum_jp_j=1$.
--   - $\rho$ minimizes the functional
--   $$
--   \mathcal G(\sigma)=c\,S\bigl((1-\kappa)\Phi(\sigma)+\kappa\tau\bigr)-a\,S(\sigma)+\beta\,E(\sigma)+\zeta\,M_4(\sigma)
--   $$
--   over all states $\sigma$ with finite fourth moment, i.e. $\mathcal G(\rho)\le\mathcal G(\sigma)$ for all such $\sigma$.
--
--   **Conclusion.** Put $k=\zeta/a$. There exist a positive bounded operator $B$ on $\mathcal F_n$, a nonempty index set $L$, a Hilbert basis $(d_l)_{l\in L}$ and numbers $u_l>0$ with $\sum_le^{-u_l}<\infty$ such that:
--   1. $W_4\,(k\,I+W_3BW_3)^{-1}\,W_4\,d_l=u_l^{-1}d_l$ for every $l$;
--   2. $\rho=\sum_l\frac{e^{-u_l}}{Z}|d_l\rangle\langle d_l|$ with $Z=\sum_le^{-u_l}$;
--   3. $\rho$ is injective (faithful) and has finite seventh moment;
--   4. for every $x\in\mathcal F_n$, in $[0,\infty]$,
--   $$
--   \operatorname{Re}\langle x,Bx\rangle=\frac{c(1-\kappa)}{a}\sum_{i\in I}\sum_{j\in J}(-\log p_j)\,|\langle b_j,V_iW_1x\rangle|^2+\frac{\beta}{a}\,N(W_1x).
--   $$
--
--   So a minimizer of the one-port entropy functional is the Gibbs state of the unbounded Hamiltonian $W_4^{-1}(k+W_3BW_3)W_4^{-1}$. The quadratic form of $B$ is the dual flow applied to $-\log\rho_0$, plus a multiple of the number operator, both seen through $W_1$. Faithfulness and the seventh-moment bound are the regularity the later variational arguments need.
--
--   **Formalization Note** Items 1–3 are the fields of the structure `GibbsData n (ζ/a) ρ`, and item 4 is stated in `ENNReal` with `ENNReal.ofReal` coefficients, which are nonnegative here. $S$ is the library's `entropy`, defined as $\sum_k\operatorname{Re}\langle k|\eta(\rho)|k\rangle$ with $\eta(t)=-t\log t$ (a `tsum`, so $0$ if the series diverges). $W_1$ is `energyInverse n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean#L698-L741

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

theorem OAI.EntropyPhotonNumber.flow_minimum_gibbs {n : ℕ} {J : Type*}
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ x,
      ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x) := by sorry
