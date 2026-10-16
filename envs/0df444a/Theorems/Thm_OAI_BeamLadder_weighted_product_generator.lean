-- Prove2me | Theorems.Thm_OAI_BeamLadder_weighted_product_generator
-- name    : OAI.BeamLadder.weighted_product_generator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:29.625358+00:00
-- url     : https://prove2.me/theorems/fee227c3-504d-4559-be59-6ea4f609b192
-- title:
--   The weighted generator pairing of a beam-splitter output splits into weighted conditional pairings of the two inputs
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
--   **Theorem.** Let $\eta \in [0,1]$, $a, b \in \mathbb{R}$, and let $\rho, \sigma, \tau$ be states such that $\tau$ is the beam-splitter output of $(\rho,\sigma)$ at $\eta$. Let $x : I \to \mathcal F_n$, $y : L \to \mathcal F_n$, $z : K \to \mathcal F_n$ be square-summable families with $\sum_i \|\Lambda^3x_i\|^2 = 1$, $\sum_l\|\Lambda^3y_l\|^2 = 1$, and
--   $$
--   \sum_i |\Lambda^3x_i\rangle\langle\Lambda^3x_i| = \rho, \qquad \sum_l |\Lambda^3y_l\rangle\langle\Lambda^3y_l| = \sigma, \qquad \sum_k |\Lambda^3z_k\rangle\langle\Lambda^3z_k| = \tau .
--   $$
--   Then for every bounded operator $B$ on $\mathcal F_n$,
--   $$
--   \mathcal G_{\eta a + (1-\eta)b}(z; B) = \mathcal G_a\big(x;\ \mathcal K_\eta[\Lambda y](B)\big) + \mathcal G_b\big(y;\ \mathcal K^R_\eta[\Lambda x](B)\big).
--   $$
--
--   This is the weighted (bounded-observable) form of the statement that the thermal generator at the interpolated parameter $\eta a + (1-\eta)b$, evaluated on the output of a beam splitter, decomposes into the generators of the two inputs at parameters $a$ and $b$, each tested against an observable conditioned on the other input. It is the key generator identity behind the beam-splitter step of the entropy photon-number argument.
--
--   **Formalization Note** $\mathcal G_r$ is `WeightedGenerator.pairing r` (with `gain j u` for $\Lambda^{-2}S_j^\mp$ and `modeBound j u` for $\Lambda^{-2}M_j^\mp$), $\mathcal K_\eta$ and $\mathcal K^R_\eta$ are `weightedConditional η hη` and `weightedConditionalRight η hη` (defined as `EnsemblePullback.pullback`, a `tsum` of compressions, with $D_{\mathrm{ten}}$ = `tensorRatioCLM`, $D_{\mathrm{ret}}$ = `retainedRatioCLM`, $B\otimes 1$ = `liftLeft B`), $U_\eta$ is `beamUnitary η hη`, states are `State n`, and the beam-splitter condition is `IsBeamSplitterOutput η ρ σ τ`. The density hypotheses use `TraceEnsemble.operator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L1606-L1660

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
variable {n : ℕ} {I J K : Type*}

theorem OAI.BeamLadder.weighted_product_generator (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op)
    (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing (η*a+(1-η)*b) z B=
      WeightedGenerator.pairing a x
        (weightedConditional η hη (fun j => inverseWeight 1 (y j)) B)+
      WeightedGenerator.pairing b y
        (weightedConditionalRight η hη (fun i => inverseWeight 1 (x i)) B) := by sorry
