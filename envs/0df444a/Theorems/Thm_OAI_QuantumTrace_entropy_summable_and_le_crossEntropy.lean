-- Prove2me | Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
-- name    : OAI.QuantumTrace.entropy_summable_and_le_crossEntropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:57:37.178546+00:00
-- url     : https://prove2.me/theorems/ce612477-0f94-42c8-9ddf-efa1aecfad88
-- title:
--   Gibbs' inequality for countable distributions: entropy is finite and at most the cross-entropy
-- statement:
--   Let $\iota$ be an arbitrary index set and let $p,q:\iota\to\mathbb{R}$ be probability distributions: $p_i\ge 0$ and $q_i>0$ for all $i$, and $\sum_ip_i=1$, $\sum_iq_i=1$ as convergent series. Write $\eta(x)=-x\log x$ (with $\eta(0)=0$). Assume that the cross-entropy series $\sum_ip_i(-\log q_i)$ converges. Then:
--
--   1. the entropy series $\sum_i\eta(p_i)$ converges, and
--   2. its sum is at most the cross-entropy:
--   $$H(p)=\sum_{i\in\iota}-p_i\log p_i\;\le\;\sum_{i\in\iota}p_i\,(-\log q_i).$$
--
--   This is Gibbs' inequality for countably supported distributions, with the finiteness of the Shannon entropy as part of the conclusion. Choosing a reference distribution $q$ whose $-\log q_i$ is an affine function of a constrained quantity, such as a thermal distribution in terms of photon number, turns it into a maximum-entropy bound under that constraint.
--
--   **Formalization Note** All sums are unconditional (`HasSum`/`Summable`), and $\eta$ is `Real.negMulLog`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L490-L507

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

theorem OAI.QuantumTrace.entropy_summable_and_le_crossEntropy {ι : Type*} (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : HasSum p 1) (hq1 : HasSum q 1)
    (hcross : Summable (fun i => p i * (-Real.log (q i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
      (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (q i)) := by sorry
