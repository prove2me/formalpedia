-- Prove2me | Theorems.Thm_OAI_CrossEnsemble_shifted_both_operator_eq
-- name    : OAI.CrossEnsemble.shifted_both_operator_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:37:05.188738+00:00
-- url     : https://prove2.me/theorems/f22563c5-7110-486c-ab12-ed3a4a692088
-- title:
--   A common coordinate substitution preserves equality of rank-one ensemble operators
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries. For a square-summable family $u = (u_i)$ in $\mathcal F_n$ let $O(u) = \sum_i |u_i\rangle\langle u_i|$ (a bounded positive operator).
--
--   **Theorem.** Let $x, y : I \to \mathcal F_n$ and $u, v : J \to \mathcal F_n$ be square-summable families, and let $f : \mathbb{N}^n \to \mathbb{N}^n$ and $c : \mathbb{N}^n \to \mathbb{C}$ be arbitrary maps such that, for all indices and all $k \in \mathbb{N}^n$,
--   $$
--   y_i(k) = c(k)\,x_i(f(k)), \qquad v_l(k) = c(k)\,u_l(f(k)).
--   $$
--   If $O(x) = O(u)$, then $O(y) = O(v)$.
--
--   Operators of the form $O(x)$ are density operators presented by column families; two different presentations of the same operator stay equivalent after the same weighted relabelling of coordinates is applied to both. Typical uses are ladder operators acting coordinatewise (shifts $k \mapsto k \pm \mathbf 1_j$ with square-root weights), so the lemma shows that such transformed operators depend only on the operator and not on the chosen family.
--
--   **Formalization Note** $O(x)$ is `CrossEnsemble.operator x x = ∑' i, rankOne ℂ (x i) (x i)`; vectors in $\mathcal F_n$ are functions on `NumberIndex n = Fin n → ℕ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L773-L795

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

open OAI OAI.CrossEnsemble
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
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

theorem OAI.CrossEnsemble.shifted_both_operator_eq (x y : I → Fock n) (u v : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (f : NumberIndex n → NumberIndex n) (c : NumberIndex n → ℂ)
    (hyx : ∀ i k, y i k=c k*x i (f k)) (hvu : ∀ j k, v j k=c k*u j (f k))
    (he : operator x x=operator u u) : operator y y=operator v v := by sorry
