-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_weakDefect_spectral
-- name    : OAI.WeightedGenerator.weakDefect_spectral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:27.715987+00:00
-- url     : https://prove2.me/theorems/559d5226-86c9-4d92-a0d9-52fd8c517148
-- title:
--   Spectral expansion of the weak defect functional in an eigenbasis
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
--   Assume moreover $\sum_r \|x_r\|^2 < \infty$. For $t \in \mathbb{R}$ and a bounded operator $Z$ on $\mathcal F_n$ define the *weak defect*
--   $$
--   \mathcal W_t(Z) = (t+1)\sum_{r \in J} \langle C^- x_r,\ Z\,\Lambda^3 x_r \rangle - t \sum_{r \in J} \langle \Lambda^3 x_r,\ Z\,C^+ x_r\rangle ,
--   $$
--   and the defect coefficient $\delta_t(p,q) = (t+1)q - tp$.
--
--   **Theorem.** The series below converges (unconditionally, over $J \times J$) and
--   $$
--   \sum_{(l,r) \in J \times J} \delta_t(p_l, p_r)\ \overline{c(l,r)}\ \langle b_l, Z b_r\rangle = \mathcal W_t(Z) .
--   $$
--
--   Thus the weak defect functional, defined through the weighted column family $x$, is the pairing of the matrix of $Z$ in the basis $(b_r)$ with the centered annihilation matrix weighted by the thermal defect coefficients. This spectral form is what allows the defect to be represented by a vector in the weighted matrix space of the thermal metric.
--
--   **Formalization Note** $\Lambda^m$ is `inverseWeight m`, $L_j$ and $R_j$ are `lowering j` and `raising j`, $C^-$ and $C^+$ are `centeredLadder j μ false` and `centeredLadder j μ true`, and $c(l,r)$ is `centeredEntry b p x j μ l r` (built from `loweringEntry`). Lean's `inner ℂ u v` is conjugate-linear in `u`. $\mathcal W_t$ is `weakDefect t x j μ Z`, built from `CrossEnsemble.pairing u v Z = ∑' i, ⟪v i, Z (u i)⟫`, and $\delta_t$ is `defectCoefficient t`. The conclusion is a `HasSum` statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L776-L812

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
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem OAI.WeightedGenerator.weakDefect_spectral (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ r, 0<p r) (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (t : ℝ) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun a : J × J => (defectCoefficient t (p a.1) (p a.2):ℂ)*
      conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)))
      (weakDefect t x j μ Z) := by sorry
