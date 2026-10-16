-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_weighted_replaced_threeport_generator
-- name    : OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:16.008691+00:00
-- url     : https://prove2.me/theorems/8333f1ec-c16f-4b68-81d4-664a2a2c9e08
-- title:
--   Weighted generator pairing for a two-stage beam-splitter cascade with thermal noise inputs
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries.
--
--   For a mode $j$ define the bounded operators
--   $$
--   (S_j^- x)(k) = \frac{\sqrt{k_j+1}}{w(k+\mathbf 1_j)^3}\,x(k+\mathbf 1_j), \quad (S_j^+ x)(k) = \frac{\sqrt{k_j}}{w(k-\mathbf 1_j)^3}\,x(k-\mathbf 1_j)\ (k_j \ge 1,\ \text{else } 0), \quad (M_j^{\mp} x)(k) = \frac{k_j + \epsilon_\mp}{w(k)^3}\,x(k),
--   $$
--   with $\epsilon_- = 0$, $\epsilon_+ = 1$; formally $S_j^- = a_j\Lambda^3$, $S_j^+ = a_j^\dagger\Lambda^3$, $M_j^- = N_j\Lambda^3$ and $M_j^+ = (N_j+1)\Lambda^3$, where $a_j, a_j^\dagger, N_j$ are the annihilation, creation and number operators of mode $j$.
--
--   For square-summable families $u = (u_i)$, $v = (v_i)$ in $\mathcal F_n$ and a bounded operator $Z$ put $\langle\!\langle u, v\rangle\!\rangle_Z = \sum_i \langle v_i, Z u_i\rangle$ and $O(u,v) = \sum_i |u_i\rangle\langle v_i|$, so that formally $\langle\!\langle u, v\rangle\!\rangle_Z = \operatorname{Tr}\big(Z\,O(u,v)\big)$.
--
--   The *generator pairing* of a square-summable family $x$ at $r \in \mathbb{R}$ is
--   $$
--   G_r(x; Z) = \sum_{j=1}^n \Big[ (r+1)\Big( \langle\!\langle S_j^-x, S_j^-x\rangle\!\rangle_Z - \tfrac12\langle\!\langle M_j^-x, \Lambda^3x\rangle\!\rangle_Z - \tfrac12\langle\!\langle \Lambda^3x, M_j^-x\rangle\!\rangle_Z \Big) + r\Big( \langle\!\langle S_j^+x, S_j^+x\rangle\!\rangle_Z - \tfrac12\langle\!\langle M_j^+x, \Lambda^3x\rangle\!\rangle_Z - \tfrac12\langle\!\langle \Lambda^3x, M_j^+x\rangle\!\rangle_Z \Big) \Big],
--   $$
--   which, for $\rho_x = O(\Lambda^3 x, \Lambda^3 x)$, is formally $\operatorname{Tr}\big(Z\,\mathcal L_r(\rho_x)\big)$ for the Lindblad generator $\mathcal L_r(\rho) = \sum_j (r+1)\big(a_j\rho a_j^\dagger - \tfrac12\{N_j, \rho\}\big) + r\big(a_j^\dagger\rho a_j - \tfrac12\{N_j+1, \rho\}\big)$ of thermal attenuation/amplification with parameter $r$. The *weighted generator pairing* $\mathcal G_r(x; Z)$ is defined by the same formula as $G_r(x;Z)$ but with $S_j^\mp$ replaced by $\Lambda^{-2}S_j^\mp$ (the bounded operators $x \mapsto w(\cdot)^2\,(S_j^\mp x)(\cdot)$), $M_j^\mp$ replaced by $\Lambda^{-2}M_j^\mp$ (multiplication by $(k_j+\epsilon_\mp)/w(k)$) and $\Lambda^3$ replaced by $\Lambda$; formally $\mathcal G_r(x;Z) = \operatorname{Tr}\big(\Lambda^{-2} Z \Lambda^{-2}\,\mathcal L_r(\rho_x)\big)$, an $(N+1)^2$-weighted form of the generator pairing.
--
--   On the two-port space $\mathcal J_n = \ell^2(\mathbb{N}^n \times \mathbb{N}^n)$ write $(u \otimes v)(k,m) = u(k)\,v(m)$ for $u, v \in \mathcal F_n$, and $W(k,m) = w(k) + w(m) - 1 = 1 + |k| + |m|$. For $\eta \in [0,1]$ let $U_\eta$ be the passive beam-splitter unitary on $\mathcal J_n$, which acts on every pair of corresponding modes by the rotation $\begin{pmatrix} \sqrt\eta & -\sqrt{1-\eta} \\ \sqrt{1-\eta} & \sqrt\eta \end{pmatrix}$ and preserves each pair's total photon number. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ with $\sum_k \operatorname{Re}\rho_{kk} = 1$. A state $\tau$ is the *beam-splitter output* of states $(\rho, \sigma)$ at $\eta$ if every entry $\tau_{kl}$ is the sum of the convergent series over $m \in \mathbb{N}^n$ of the explicit finite block sums that describe $\langle e_k \otimes e_m,\ U_\eta(\rho\otimes\sigma)U_\eta^{*}\,(e_l\otimes e_m)\rangle$; that is, $\tau$ is the reduced state of the first output port.
--
--   Let $D_{\mathrm{ten}}$ and $D_{\mathrm{ret}}$ be the diagonal operators on $\mathcal J_n$ multiplying the $(k,m)$ coordinate by $\big(W(k,m)/(w(k)w(m))\big)^2$ and $\big(w(k)/W(k,m)\big)^2$. For a square-summable family $y' = (y'_l)$ in $\mathcal F_n$ and a bounded $B$ on $\mathcal F_n$ define the *weighted conditionals*
--   $$
--   \mathcal K_\eta[y'](B) = \sum_l V_l^{*}(B \otimes 1)V_l, \qquad \mathcal K^{R}_\eta[y'](B) = \sum_l V_l'^{*}(B\otimes 1)V'_l,
--   $$
--   where $V_l u = D_{\mathrm{ret}}U_\eta D_{\mathrm{ten}}(u \otimes y'_l)$ and $V'_l u = D_{\mathrm{ret}}U_\eta D_{\mathrm{ten}}(y'_l \otimes u)$, and $B\otimes 1$ acts on the first factor.
--
--   A *weighted column representation* $X$ of a state $\rho$ is a family $(X_i)$ in $\mathcal F_n$ with $\sum_i\|X_i\|^2 < \infty$, $\sum_i \|\Lambda^3X_i\|^2 = 1$ and $\sum_i|\Lambda^3X_i\rangle\langle\Lambda^3X_i| = \rho$; its slices are $X.\mathrm{sl}_\eta(B) = \mathcal K_\eta[\Lambda X](B)$ and $X.\mathrm{sl}^R_\eta(B) = \mathcal K^R_\eta[\Lambda X](B)$. The thermal weight with mean photon number $s$ per mode is $\pi_s(k) = \prod_{j=1}^n (s+1)^{-1}\big(s/(s+1)\big)^{k_j}$.
--
--   **Theorem.** Let $\eta, \theta \in [0,1]$ and $\kappa, a, b, d \in \mathbb{R}$ with $d > 0$, and put
--   $$
--   r_0 = \theta\big(\eta a + (1-\eta)b\big) + (1-\theta)d, \qquad\text{assumed } r_0 > 0 .
--   $$
--   Let $\rho, \sigma, \tau_D, m, \gamma, \omega, \rho_0$ be states such that $m$ is the beam-splitter output of $(\rho,\sigma)$ at $\eta$, $\gamma$ is the beam-splitter output of $(m, \tau_D)$ at $\theta$, $\tau_D$ and $\omega$ are the diagonal thermal states $(\tau_D)_{kl} = [k=l]\,\pi_d(k)$ and $\omega_{kl} = [k=l]\,\pi_{r_0}(k)$, and $\rho_0 = (1-\kappa)\gamma + \kappa\,\omega$. Let $X, Y, D, M, \Gamma, \Omega, Z$ be weighted column representations of $\rho, \sigma, \tau_D, m, \gamma, \omega, \rho_0$. Then for every bounded operator $B$ on $\mathcal F_n$,
--   $$
--   \mathcal G_{r_0}(Z; B) = (1-\kappa)\Big[ \mathcal G_a\big(X;\ Y.\mathrm{sl}_\eta(D.\mathrm{sl}_\theta(B))\big) + \mathcal G_b\big(Y;\ X.\mathrm{sl}^R_\eta(D.\mathrm{sl}_\theta(B))\big) \Big].
--   $$
--
--   The state $\rho_0$ arises by mixing the two inputs at a first beam splitter, mixing the result with thermal noise at a second one, and then replacing a fraction $\kappa$ of the output by the thermal state at the matching parameter $r_0$. The identity shows that the weighted generator pairing of $\rho_0$ only sees the two original inputs, each tested against a nested weighted conditional observable; the thermal ingredients drop out.
--
--   **Formalization Note** Weighted column representations are `EntropyPhotonNumber.WeightedColumns ρ` (fields `vector`, `summable`, `normalized`, `density`), the slices are `X.slice η hη` and `X.sliceRight η hη`, $\mathcal G_r$ is `WeightedGenerator.pairing r`, $\pi_s$ is `QuantumTrace.thermalWeight n s`, and the beam-splitter conditions are `IsBeamSplitterOutput`. No sign condition on $\kappa$ is imposed; the mixture hypothesis is the operator identity `ρ0.op = ((1-κ:ℝ):ℂ) • γ.op + (κ:ℂ) • ω.op`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L339-L369

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
open QuantumTrace Annihilation BeamLadder

theorem OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (Z : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=
      if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hZ : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing (θ*(η*a+(1-η)*b)+(1-θ)*d) Z.vector B=
      ((1-κ:ℝ):ℂ)*(WeightedGenerator.pairing a X.vector (Y.slice η hη (D.slice θ hθ B))+
        WeightedGenerator.pairing b Y.vector (X.sliceRight η hη (D.slice θ hθ B))) := by sorry
