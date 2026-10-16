-- Prove2me | Theorems.Thm_OAI_PhysicalGenerator_pairing_hasSum
-- name    : OAI.PhysicalGenerator.pairing_hasSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:58.314974+00:00
-- url     : https://prove2.me/theorems/031cffa2-13ae-4d06-9dc9-e7e0818b6242
-- title:
--   The trace of an observable against the generator operator equals the generator pairing in every orthonormal basis
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
--   For a mode $j$ define the dissipator operators
--   $$
--   \mathcal D_j^-(x) = O(S_j^-x, S_j^-x) - \tfrac12\big(O(M_j^-x, \Lambda^3x) + O(\Lambda^3x, M_j^-x)\big),
--   $$
--   and $\mathcal D_j^+(x)$ likewise with $S_j^+$, $M_j^+$, and the generator operator $\mathcal L_r(x) = \sum_j \big((r+1)\mathcal D_j^-(x) + r\,\mathcal D_j^+(x)\big)$ (formally $\mathcal L_r(\rho_x)$ with $\rho_x = O(\Lambda^3x,\Lambda^3x)$).
--
--   **Theorem.** Let $(b_s)_{s\in J}$ be any orthonormal basis of $\mathcal F_n$, $r \in \mathbb{R}$, $x : I \to \mathcal F_n$ a family with $\sum_i\|x_i\|^2 < \infty$, and $Z$ a bounded operator. Then the series converges and
--   $$
--   \sum_{s \in J} \big\langle b_s,\ Z\,\mathcal L_r(x)\,b_s\big\rangle = G_r(x; Z).
--   $$
--
--   The generator pairing $G_r(x;Z)$ is thus the trace $\operatorname{Tr}(Z\,\mathcal L_r(x))$, computed in any orthonormal basis. This identifies the pairing, defined through column families, with a genuine trace of a bounded operator against the generator.
--
--   **Formalization Note** $\mathcal L_r(x)$ is `PhysicalGenerator.generator r x` (built from `PhysicalGenerator.dissipator`, `lowerFamily`, `raiseFamily`, `modeFamily`, `baseFamily`), $G_r$ is `singleGeneratorPairing r x Z`, and $O(u,v)$ is `CrossEnsemble.operator u v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L42-L63

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

open OAI OAI.PhysicalGenerator
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
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

theorem OAI.PhysicalGenerator.pairing_hasSum {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (generator r x (b k)))) (singleGeneratorPairing r x Z) := by sorry
