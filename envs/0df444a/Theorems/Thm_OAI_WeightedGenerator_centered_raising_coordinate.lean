-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_centered_raising_coordinate
-- name    : OAI.WeightedGenerator.centered_raising_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:31:52.468521+00:00
-- url     : https://prove2.me/theorems/e0b78caa-4efa-44f9-9c1f-934035db0660
-- title:
--   Spectral coordinates of the centered raising ladder are conjugates of the centered annihilation matrix
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$ and let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m} x(k)$, so that formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$. For a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index, and let $L_j$, $R_j$ be the bounded weighted ladder operators
--   $$
--   (L_j x)(k) = \frac{\sqrt{k_j+1}}{w(k+\mathbf 1_j)}\, x(k+\mathbf 1_j), \qquad (R_j x)(k) = \frac{\sqrt{k_j}}{w(k-\mathbf 1_j)}\, x(k-\mathbf 1_j)\ \ (k_j \ge 1), \quad (R_j x)(k) = 0\ \ (k_j = 0),
--   $$
--   that is, formally $L_j = a_j\Lambda$ and $R_j = a_j^\dagger \Lambda$ with the annihilation and creation operators $a_j, a_j^\dagger$ of mode $j$.
--
--   Let $(b_r)_{r \in J}$ be an orthonormal (Hilbert) basis of $\mathcal F_n$, let $p : J \to (0,\infty)$, and let $x : J \to \mathcal F_n$ be a family with $\Lambda^3 x_r = \sqrt{p_r}\, b_r$ for every $r \in J$. For a mode $j$ and $\mu \in \mathbb{C}$ define the centered ladder operators $C^- = (L_j - \mu\Lambda)\Lambda^2$ and $C^+ = (R_j - \bar\mu\Lambda)\Lambda^2$ and the centered matrix
--   $$
--   c(l,r) = \frac{\langle b_l,\ L_j\Lambda^2 x_r\rangle}{\sqrt{p_r}} - \mu\,[l = r] \qquad (l, r \in J),
--   $$
--   where $[l=r]$ is $1$ if $l = r$ and $0$ otherwise. Formally $C^- x_r = \sqrt{p_r}\,(a_j - \mu) b_r$, $C^+ x_r = \sqrt{p_r}\,(a_j^\dagger - \bar\mu) b_r$ and $c(l,r) = \langle b_l, (a_j - \mu) b_r\rangle$, the matrix of the centered annihilation operator in the basis $(b_r)$.
--
--   **Theorem.** For all $l, r \in J$,
--   $$
--   \langle b_r,\ C^+ x_l \rangle = \sqrt{p_l}\ \overline{c(l,r)} .
--   $$
--
--   This is the weighted, bounded-operator form of the adjoint relation $(a_j - \mu)^\dagger = a_j^\dagger - \bar\mu$ expressed in the spectral basis: the coordinates of the centered raising operator are read off from the centered annihilation matrix. It is the input for the norm and trace identities relating the two centered ladders.
--
--   **Formalization Note** $\Lambda^m$ is `inverseWeight m`, $L_j$ and $R_j$ are `lowering j` and `raising j`, $C^-$ and $C^+$ are `centeredLadder j μ false` and `centeredLadder j μ true`, and $c(l,r)$ is `centeredEntry b p x j μ l r` (built from `loweringEntry`). Lean's `inner ℂ u v` is conjugate-linear in `u`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L545-L564

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
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

theorem OAI.WeightedGenerator.centered_raising_coordinate (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b r) (centeredLadder j μ true (x l))=
      (Real.sqrt (p l):ℂ)*conj (centeredEntry b p x j μ l r) := by sorry
