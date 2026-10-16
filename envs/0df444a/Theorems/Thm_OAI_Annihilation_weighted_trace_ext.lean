-- Prove2me | Theorems.Thm_OAI_Annihilation_weighted_trace_ext
-- name    : OAI.Annihilation.weighted_trace_ext
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:38:54.860214+00:00
-- url     : https://prove2.me/theorems/1018b710-bfdb-4d0a-876f-8c22bf63af26
-- title:
--   Trace functionals that agree on all $(N+1)^{-2}$-sandwiched observables agree everywhere
-- statement:
--   Let $\mathcal F_n = \ell^2(\mathbb{N}^n)$ be the $n$-mode Fock space with number basis $(e_k)_{k \in \mathbb{N}^n}$ and inner product $\langle u, v\rangle = \sum_k \overline{u(k)}\,v(k)$ (conjugate-linear in the first slot). Put $w(k) = 1 + k_1 + \dots + k_n$, let $\Lambda^m$ be the bounded diagonal operator $(\Lambda^m x)(k) = w(k)^{-m}x(k)$ (formally $\Lambda = (N+1)^{-1}$ for the total number operator $N$), and for a mode $j$ let $\mathbf 1_j \in \mathbb{N}^n$ be the $j$-th unit index; $k - \mathbf 1_j$ lowers the $j$-th entry by one, truncated at $0$. Write $|u\rangle\langle v|$ for the rank-one operator $y \mapsto \langle v, y\rangle\,u$, and $T_{kl} = \langle e_k, T e_l\rangle$ for number-basis matrix entries.
--
--   **Theorem.** Let $(b_s)_{s\in J}$ be an orthonormal basis of $\mathcal F_n$, let $A, Q$ be bounded operators on $\mathcal F_n$, and let $f, g$ be functions from bounded operators on $\mathcal F_n$ to $\mathbb{C}$ such that for every bounded $Z$ the series below converge with
--   $$
--   \sum_{s} \langle b_s, Z A b_s\rangle = f(Z), \qquad \sum_s \langle b_s, Z Q b_s\rangle = g(Z).
--   $$
--   If $f(\Lambda^2 Z\Lambda^2) = g(\Lambda^2 Z\Lambda^2)$ for every bounded $Z$, then $f(Z) = g(Z)$ for every bounded $Z$.
--
--   In other words, a functional given by a trace-type formula $Z \mapsto \operatorname{Tr}(ZA)$ is determined by its values on observables of the form $(N+1)^{-2}Z(N+1)^{-2}$. This allows identities between weighted generator pairings to be verified only on sandwiched observables, where they reduce to unweighted (physical) identities.
--
--   **Formalization Note** $\Lambda^2$ is `inverseWeight 2`; the hypotheses are `HasSum` statements in the basis `b : HilbertBasis J ℂ (Fock n)`, and `Λ² Z Λ²` is `inverseWeight 2 ∘L Z ∘L inverseWeight 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean#L1327-L1349

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

open OAI OAI.Annihilation
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
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

theorem OAI.Annihilation.weighted_trace_ext {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (A Q : Fock n →L[ℂ] Fock n)
    (f g : (Fock n →L[ℂ] Fock n) → ℂ)
    (hf : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (A (b k)))) (f Z))
    (hg : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (Q (b k)))) (g Z))
    (h : ∀ Z, f (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
      g (inverseWeight 2 ∘L Z ∘L inverseWeight 2)) : ∀ Z, f Z=g Z := by sorry
