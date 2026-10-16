-- Prove2me | Theorems.Thm_OAI_PhysicalGenerator_dissipator_entry
-- name    : OAI.PhysicalGenerator.dissipator_entry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:40:31.636825+00:00
-- url     : https://prove2.me/theorems/7899f7fa-f8bb-413c-b59e-63ec7519be6c
-- title:
--   Number-basis matrix entries of the single-mode dissipators
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries.
--
--   For a mode $j$ define the bounded operators
--   $$
--   (S_j^- x)(k) = \frac{\sqrt{k_j+1}}{w(k+\mathbf 1_j)^3}\,x(k+\mathbf 1_j), \quad (S_j^+ x)(k) = \frac{\sqrt{k_j}}{w(k-\mathbf 1_j)^3}\,x(k-\mathbf 1_j)\ (k_j \ge 1,\ \text{else } 0), \quad (M_j^{\mp} x)(k) = \frac{k_j + \epsilon_\mp}{w(k)^3}\,x(k),
--   $$
--   with $\epsilon_- = 0$, $\epsilon_+ = 1$; formally $S_j^- = a_j\Lambda^3$, $S_j^+ = a_j^\dagger\Lambda^3$, $M_j^- = N_j\Lambda^3$ and $M_j^+ = (N_j+1)\Lambda^3$, where $a_j, a_j^\dagger, N_j$ are the annihilation, creation and number operators of mode $j$.
--
--   For a square-summable family $x$ put $O(u,v) = \sum_i |u_i\rangle\langle v_i|$, $\rho = O(\Lambda^3x, \Lambda^3x)$, and for a mode $j$ define the dissipators
--   $$
--   \mathcal D_j^{-} = O(S_j^-x, S_j^-x) - \tfrac12\big(O(M_j^-x,\Lambda^3x) + O(\Lambda^3x, M_j^-x)\big), \qquad \mathcal D_j^{+} = O(S_j^+x, S_j^+x) - \tfrac12\big(O(M_j^+x,\Lambda^3x) + O(\Lambda^3x, M_j^+x)\big).
--   $$
--   Let $\lambda_j(k) = \sqrt{k_j+1}$, $\kappa_j(k) = \sqrt{k_j}$ (set to $0$ when $k_j = 0$) and $\nu_j^{\mp}(k) = k_j + \epsilon_\mp$ with $\epsilon_- = 0$, $\epsilon_+ = 1$.
--
--   **Theorem.** If $\sum_i\|x_i\|^2 < \infty$, then for every mode $j$ and all $k, l \in \mathbb{N}^n$,
--   $$
--   (\mathcal D_j^-)_{kl} = \lambda_j(k)\,\overline{\lambda_j(l)}\,\rho_{k+\mathbf 1_j,\,l+\mathbf 1_j} - \tfrac12\big(\nu_j^-(k) + \overline{\nu_j^-(l)}\big)\rho_{kl},
--   $$
--   $$
--   (\mathcal D_j^+)_{kl} = \kappa_j(k)\,\overline{\kappa_j(l)}\,\rho_{k-\mathbf 1_j,\,l-\mathbf 1_j} - \tfrac12\big(\nu_j^+(k) + \overline{\nu_j^+(l)}\big)\rho_{kl}.
--   $$
--
--   These are the matrix entries of $a_j\rho a_j^\dagger - \tfrac12\{N_j, \rho\}$ and $a_j^\dagger\rho a_j - \tfrac12\{N_j + 1, \rho\}$, expressed through the entries of $\rho$ only. They make the dissipators computable in the number basis and are used, for instance, to verify that diagonal thermal states are annihilated by the generator.
--
--   **Formalization Note** The statement is `PhysicalGenerator.dissipator_entry` with a Boolean `u` selecting $\mathcal D_j^+$ (`u = true`) or $\mathcal D_j^-$ (`u = false`); $\lambda_j, \kappa_j, \nu_j^\mp$ are `lowerCoefficient`, `raiseCoefficient`, `modeCoefficient`, $\rho$ is `CrossEnsemble.operator (baseFamily x) (baseFamily x)`, $k \pm \mathbf 1_j$ are `up j k` and `down j k`, and entries are `entry T k l`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L65-L115

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

theorem OAI.PhysicalGenerator.dissipator_entry (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (j : Fin n) (u : Bool) (k l : NumberIndex n) :
    entry (dissipator j u x) k l =
      (if u then raiseCoefficient j k*conj (raiseCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (down j k) (down j l)
      else lowerCoefficient j k*conj (lowerCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (up j k) (up j l))-
      (2:ℂ)⁻¹*((modeCoefficient j u k+conj (modeCoefficient j u l))*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l) := by sorry
