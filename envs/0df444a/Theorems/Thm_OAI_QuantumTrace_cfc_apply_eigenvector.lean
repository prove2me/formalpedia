-- Prove2me | Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
-- name    : OAI.QuantumTrace.cfc_apply_eigenvector
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:54:40.451994+00:00
-- url     : https://prove2.me/theorems/1c91603b-9d03-4acb-9672-3b048325a406
-- title:
--   Continuous functional calculus acts on an eigenvector by evaluation at its eigenvalue
-- statement:
--   Let $E$ be a complex Hilbert space and let $T:E\to E$ be a bounded symmetric (self-adjoint) operator. Let $x\in E$ and $\mu\in\mathbb{C}$ satisfy $Tx=\mu x$, and let $f:\mathbb{C}\to\mathbb{C}$ be continuous on the spectrum $\sigma(T)$. Then the continuous functional calculus $f(T)$ satisfies
--   $$f(T)\,x=f(\mu)\,x .$$
--
--   The identity covers $x=0$ trivially; for $x\neq 0$ it says that eigenvectors of $T$ remain eigenvectors of every continuous function of $T$, with eigenvalue transformed by $f$. It is used to compute operators such as $-T\log T$ on an eigenbasis of a density operator.
--
--   **Formalization Note** $f(T)$ is Mathlib's `cfc f T`, which is well defined here because a self-adjoint operator is normal and $f$ is continuous on $\sigma(T)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L297-L331

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.QuantumTrace.cfc_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {μ : ℂ} (he : T x = μ • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ T)) : cfc f T x = f μ • x := by sorry
