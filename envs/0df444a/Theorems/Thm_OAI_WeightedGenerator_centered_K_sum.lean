-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_centered_K_sum
-- name    : OAI.WeightedGenerator.centered_K_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:32:53.826691+00:00
-- url     : https://prove2.me/theorems/5afc721b-da52-441c-a4f8-5b6fb7485c38
-- title:
--   A thermal quadratic form in the centered annihilation matrices reduces to centered ladder norms minus $nt$
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$ and let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m} x(k)$, so that formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$. For a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index, and let $L_j$, $R_j$ be the bounded weighted ladder operators
--   $$
--   (L_j x)(k) = \frac{\sqrt{k_j+1}}{w(k+\mathbf 1_j)}\, x(k+\mathbf 1_j), \qquad (R_j x)(k) = \frac{\sqrt{k_j}}{w(k-\mathbf 1_j)}\, x(k-\mathbf 1_j)\ \ (k_j \ge 1), \quad (R_j x)(k) = 0\ \ (k_j = 0),
--   $$
--   that is, formally $L_j = a_j\Lambda$ and $R_j = a_j^\dagger \Lambda$ with the annihilation and creation operators $a_j, a_j^\dagger$ of mode $j$.
--
--   Let $(b_r)_{r\in J}$ be an orthonormal basis of $\mathcal F_n$, $p : J \to (0,\infty)$, and $x : J \to \mathcal F_n$ a family with $\sum_r \|x_r\|^2 < \infty$, $\Lambda^3 x_r = \sqrt{p_r}\,b_r$ for every $r$, and $\sum_r \|\Lambda^3 x_r\|^2 = 1$ (equivalently $\sum_r p_r = 1$). For a vector $\mu = (\mu_1, \dots, \mu_n) \in \mathbb{C}^n$ and each mode $j$ define $C_j^- = (L_j - \mu_j\Lambda)\Lambda^2$ and the centered matrix $c_j(l,r) = \langle b_l, L_j\Lambda^2 x_r\rangle/\sqrt{p_r} - \mu_j\,[l = r]$ (formally the matrix of $a_j - \mu_j$ in the basis $(b_r)$).
--
--   **Theorem.** For every $t \in \mathbb{R}$,
--   $$
--   \sum_{j=1}^{n} \sum_{(l,r) \in J \times J} \big( (t+1)\,p_r - t\,p_l \big)\, |c_j(l,r)|^2 = \sum_{j=1}^{n} \sum_{r \in J} \|C_j^- x_r\|^2 - n\,t .
--   $$
--
--   With $\rho = \sum_r p_r |b_r\rangle\langle b_r|$, the left side is the quadratic form of the centered annihilation operators weighted by the thermal defect coefficients $(t+1)p_r - tp_l$; the identity removes the $t$-dependence up to the constant $-nt$, which comes from the canonical commutation relations $[a_j, a_j^\dagger] = 1$.
--
--   **Formalization Note** $\Lambda^m$ is `inverseWeight m`, $L_j$ is `lowering j`, $C_j^-$ is `centeredLadder j (μ j) false` and $c_j$ is `centeredEntry b p x j (μ j)`. The double series are Lean `tsum`s over `J × J` and `J`; the proof establishes their summability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L612-L632

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

theorem OAI.WeightedGenerator.centered_K_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (hn : HasSum (fun r => ‖inverseWeight 3 (x r)‖^2) 1) (μ : Fin n → ℂ) (t : ℝ) :
    (∑ j, ∑' a : J × J, ((t+1)*p a.2-t*p a.1)*‖centeredEntry b p x j (μ j) a.1 a.2‖^2)=
      (∑ j, ∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)-(n:ℝ)*t := by sorry
