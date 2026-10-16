-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_weakDefect_numberMatrixUnit
-- name    : OAI.WeightedGenerator.weakDefect_numberMatrixUnit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:34:10.853925+00:00
-- url     : https://prove2.me/theorems/f0a18a65-ac41-469a-bee2-32ac9209ed42
-- title:
--   The weak defect functional on number-basis matrix units in terms of the density matrix
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries. Let $L_j$, $R_j$ be the bounded weighted ladder operators $(L_jx)(k) = \sqrt{k_j+1}\,w(k+\mathbf 1_j)^{-1}x(k+\mathbf 1_j)$ and $(R_jx)(k) = \sqrt{k_j}\,w(k-\mathbf 1_j)^{-1}x(k-\mathbf 1_j)$ for $k_j \ge 1$, $(R_jx)(k) = 0$ for $k_j = 0$ (formally $a_j\Lambda$ and $a_j^\dagger\Lambda$).
--
--   Let $x : J \to \mathcal F_n$ satisfy $\sum_r \|x_r\|^2 < \infty$, and let $\rho$ be a state (a positive bounded operator with $\sum_k \operatorname{Re}\rho_{kk} = 1$) with $\rho = \sum_r |\Lambda^3x_r\rangle\langle\Lambda^3x_r|$. For a mode $j$, $\mu \in \mathbb{C}$ and $t \in \mathbb{R}$ let $C^- = (L_j - \mu\Lambda)\Lambda^2$, $C^+ = (R_j - \bar\mu\Lambda)\Lambda^2$, and define the weak defect of a bounded operator $Z$ by
--   $$
--   \mathcal W_t(Z) = (t+1)\sum_r \langle C^-x_r,\ Z\,\Lambda^3x_r\rangle - t\sum_r\langle \Lambda^3x_r,\ Z\,C^+x_r\rangle .
--   $$
--
--   **Theorem.** For all $a, b \in \mathbb{N}^n$, with the matrix unit $E_{ab} = |e_a\rangle\langle e_b|$,
--   $$
--   \mathcal W_t(E_{ab}) = (t+1)\sqrt{a_j+1}\ \rho_{b,\,a+\mathbf 1_j} - t\sqrt{b_j}\ \rho_{b-\mathbf 1_j,\,a} - \bar\mu\,\rho_{b,a} .
--   $$
--
--   The weak defect is thus determined by explicit, finitely many entries of $\rho$ on each matrix unit; formally it is the trace of $Z$ against $(t+1)\rho\,(a_j - \mu)^\dagger - t\,(a_j^\dagger - \bar\mu)\rho$. This entrywise formula identifies the abstract functional with a concrete number-basis expression independent of the chosen column family $x$.
--
--   **Formalization Note** $\mathcal W_t$ is `WeightedGenerator.weakDefect t x j μ Z` with $C^\mp$ = `centeredLadder j μ false/true`, $E_{ab}$ is `numberMatrixUnit a b`, $\rho_{kl}$ is `entry ρ.op k l`, $a + \mathbf 1_j$ is `up j a` and $b - \mathbf 1_j$ is `down j b` (natural-number subtraction; when $b_j = 0$ the factor $\sqrt{b_j}$ vanishes). The density hypothesis is `CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j)) = ρ.op`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L981-L1018

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

open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem OAI.WeightedGenerator.weakDefect_numberMatrixUnit (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun j => ‖x j‖^2)) (ρ : State n)
    (he : CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j))=ρ.op)
    (j : Fin n) (μ : ℂ) (a b : NumberIndex n) :
    weakDefect t x j μ (numberMatrixUnit a b)=
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-
      (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-
      conj μ*entry ρ.op b a := by sorry
