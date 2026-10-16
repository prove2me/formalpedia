-- Prove2me | Theorems.Thm_OAI_BeamLadder_generatorPairingL_product
-- name    : OAI.BeamLadder.generatorPairingL_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:36:41.384113+00:00
-- url     : https://prove2.me/theorems/0bf20389-892a-4b34-bd95-72e47ccf6588
-- title:
--   The left-port generator pairing of a product ensemble equals the one-port pairing of the conditional observable
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
--   which, for $\rho_x = O(\Lambda^3 x, \Lambda^3 x)$, is formally $\operatorname{Tr}\big(Z\,\mathcal L_r(\rho_x)\big)$ for the Lindblad generator $\mathcal L_r(\rho) = \sum_j (r+1)\big(a_j\rho a_j^\dagger - \tfrac12\{N_j, \rho\}\big) + r\big(a_j^\dagger\rho a_j - \tfrac12\{N_j+1, \rho\}\big)$ of thermal attenuation/amplification with parameter $r$.
--
--   On the two-port space $\mathcal J_n = \ell^2(\mathbb{N}^n \times \mathbb{N}^n)$ write $(u \otimes v)(k,m) = u(k)\,v(m)$ for $u, v \in \mathcal F_n$, and $W(k,m) = w(k) + w(m) - 1 = 1 + |k| + |m|$. On the first port define, for a mode $j$, the bounded operators
--   $$
--   (A_jX)(k,m) = \frac{\sqrt{k_j+1}}{W(k,m)+1}\,X(k+\mathbf 1_j, m), \qquad (VX)(k,m) = \frac{X(k,m)}{W(k,m)},
--   $$
--   $R_j = \iota(W)A_j^{*}$ with $\iota(W) = W/(W-1)$ for $W > 1$ and $0$ otherwise, $P_j^- = A_j(I - V)$ and $P_j^+ = R_j(I + V)$ (formally $A_j = a_jW^{-1}$, $R_j = a_j^\dagger W^{-1}$ on the first port). For $X, Y \in \mathcal J_n$ and a bounded $Z$ on $\mathcal J_n$ let
--   $$
--   q_j^-(X,Y;Z) = \langle A_jVX,\ ZA_jVY\rangle - \tfrac12\big(\langle V^2X,\ ZR_jP_j^-Y\rangle + \langle R_jP_j^-X,\ ZV^2Y\rangle\big),
--   $$
--   and $q_j^+$ the same with $(A_j, R_jP_j^-)$ replaced by $(R_j, A_jP_j^+)$. For families $X = (X_s)$, $Y = (Y_s)$ the left-port generator pairing is $\Gamma_r(X,Y;Z) = \sum_j\big[(r+1)\sum_s q_j^-(X_s,Y_s;Z) + r\sum_s q_j^+(X_s,Y_s;Z)\big]$.
--
--   Let
--   $$
--   T(x,y) = \Lambda x \otimes \Lambda^3 y + \Lambda^3 x\otimes \Lambda y + \Lambda^3x\otimes\Lambda^3y + 2\Lambda^2x\otimes\Lambda^2y - 2\Lambda^2x\otimes\Lambda^3y - 2\Lambda^3x\otimes\Lambda^2y
--   $$
--   be the second tensor preimage. For a family $(c_s)$ in $\mathcal F_n$ with $\sum_s\|c_s\|^2 = 1$ the conditional observable on the first port is $\mathcal E_c(Z) = \sum_s E_s^{*}ZE_s$ with $E_su = u \otimes c_s$ (contraction of the second port against the state $\sum_s |c_s\rangle\langle c_s|$).
--
--   **Theorem.** Let $r \in \mathbb{R}$ and let $(x_i)_{i\in I}$, $(y_l)_{l\in L}$ be square-summable families in $\mathcal F_n$ with $\sum_l \|\Lambda^3y_l\|^2 = 1$. Then for every bounded operator $Z$ on $\mathcal J_n$, with $X_{(i,l)} = T(x_i, y_l)$,
--   $$
--   \Gamma_r(X, X; Z) = G_r\big(x;\ \mathcal E_{\Lambda^3y}(Z)\big).
--   $$
--
--   For the product ensemble whose $W^{-2}$-image is $\Lambda^3x_i\otimes\Lambda^3y_l$, the left-port generator acting on the joint system is seen by any observable exactly as the one-port generator of the first input, tested against the conditional observable obtained by averaging over the other port. This is one half of the decomposition of the two-port generator used to compare a beam-splitter output with its inputs.
--
--   **Formalization Note** $\Gamma_r$ is `generatorPairingL` (with `quadMinusL`, `quadPlusL`), $A_j$, $R_j$, $P_j^\mp$, $V$ are `lowerL`, `raiseL`, `preLowerL`, `preRaiseL`, `inverse`; $T$ is `tensorPreimage2`; $G_r$ is `singleGeneratorPairing r` with $S_j^-$ = `sandwich 0 3`, $S_j^+$ = `creationSandwich 0 3`, $M_j^\mp$ = `inverseWeight 2 ∘ modeBound j false/true`; $\mathcal E_c$ is `TensorLp.conditionalLeft` (a Kraus-type dual `KrausBounded.dual`); the normalization is the `HasSum … 1` hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L714-L765

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

open OAI OAI.BeamLadder
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
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

theorem OAI.BeamLadder.generatorPairingL_product (r : ℝ) (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : JointFock n →L[ℂ] JointFock n) :
    generatorPairingL r (fun ij : I × J => tensorPreimage2 (x ij.1) (y ij.2))
      (fun ij : I × J => tensorPreimage2 (x ij.1) (y ij.2)) Z=
      singleGeneratorPairing r x (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn Z) := by sorry
