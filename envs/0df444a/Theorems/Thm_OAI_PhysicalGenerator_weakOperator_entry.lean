-- Prove2me | Theorems.Thm_OAI_PhysicalGenerator_weakOperator_entry
-- name    : OAI.PhysicalGenerator.weakOperator_entry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:50.847764+00:00
-- url     : https://prove2.me/theorems/aa2a8983-d4e5-4d31-abab-15b44201a213
-- title:
--   Number-basis matrix entries of the weak generator operator
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries.
--
--   For a mode $j$ define the bounded operators
--   $$
--   (S_j^- x)(k) = \frac{\sqrt{k_j+1}}{w(k+\mathbf 1_j)^3}\,x(k+\mathbf 1_j), \quad (S_j^+ x)(k) = \frac{\sqrt{k_j}}{w(k-\mathbf 1_j)^3}\,x(k-\mathbf 1_j)\ (k_j \ge 1,\ \text{else } 0), \quad (M_j^{\mp} x)(k) = \frac{k_j + \epsilon_\mp}{w(k)^3}\,x(k),
--   $$
--   with $\epsilon_- = 0$, $\epsilon_+ = 1$; formally $S_j^- = a_j\Lambda^3$, $S_j^+ = a_j^\dagger\Lambda^3$, $M_j^- = N_j\Lambda^3$ and $M_j^+ = (N_j+1)\Lambda^3$, where $a_j, a_j^\dagger, N_j$ are the annihilation, creation and number operators of mode $j$.
--
--   For a square-summable family $x$ put $O(u,v) = \sum_i |u_i\rangle\langle v_i|$ and $\rho = O(\Lambda^3x,\Lambda^3x)$. For $r \in \mathbb{R}$ and a mode $j$ define the weak operator
--   $$
--   \mathcal V_{r,j}(x) = (r+1)\,O(\Lambda^3x,\ S_j^-x) - r\,O(S_j^+x,\ \Lambda^3x),
--   $$
--   formally $(r+1)\rho\,a_j^\dagger - r\,a_j^\dagger\rho$. Let $\lambda_j(l) = \sqrt{l_j+1}$ and $\kappa_j(k) = \sqrt{k_j}$ (set to $0$ when $k_j = 0$).
--
--   **Theorem.** If $\sum_i\|x_i\|^2 < \infty$, then for all $k, l \in \mathbb{N}^n$,
--   $$
--   \big(\mathcal V_{r,j}(x)\big)_{kl} = (r+1)\,\overline{\lambda_j(l)}\,\rho_{k,\,l+\mathbf 1_j} - r\,\kappa_j(k)\,\rho_{k-\mathbf 1_j,\,l} .
--   $$
--
--   The weak operator encodes the first-order (drift) part of the thermal generator in a mode; its entries are explicit shifts of the entries of $\rho$, which makes it computable in the number basis and independent of the chosen column family.
--
--   **Formalization Note** $\mathcal V_{r,j}$ is `PhysicalGenerator.weakOperator r j x`, $S_j^-x$ and $S_j^+x$ are `lowerFamily j x` and `raiseFamily j x`, $\Lambda^3x$ is `baseFamily x`, $\lambda_j$, $\kappa_j$ are `lowerCoefficient`, `raiseCoefficient`, and $k \pm \mathbf 1_j$ are `up j`, `down j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L394-L418

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
variable {n : ℕ} {I J K : Type*}

theorem OAI.PhysicalGenerator.weakOperator_entry (r : ℝ) (j : Fin n) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (k l : NumberIndex n) :
    entry (weakOperator r j x) k l=
      (r+1:ℂ)*conj (lowerCoefficient j l)*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k (up j l)-
      (r:ℂ)*raiseCoefficient j k*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (down j k) l := by sorry
