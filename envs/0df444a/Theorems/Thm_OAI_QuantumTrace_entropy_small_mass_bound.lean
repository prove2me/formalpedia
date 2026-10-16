-- Prove2me | Theorems.Thm_OAI_QuantumTrace_entropy_small_mass_bound
-- name    : OAI.QuantumTrace.entropy_small_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:58:43.419316+00:00
-- url     : https://prove2.me/theorems/21c86211-c53d-4c34-90a4-33ceb02cf8de
-- title:
--   Entropy bound for a subnormalized finite-energy distribution of small total mass
-- statement:
--   Let $n\in\mathbb{N}$ and let $p:\mathbb{N}^n\to\mathbb{R}$ satisfy $0\le p_k\le 1$ for all $k$. Suppose the series $\sum_kp_k$ converges with sum $q$, and the energy series $\sum_k|k|\,p_k$ converges, where $|k|=k_1+\dots+k_n$; write $N=\sum_k|k|\,p_k$. Let $\eta(x)=-x\log x$ (with $\eta(0)=0$). Then:
--
--   1. the series $\sum_k\eta(p_k)$ converges, and
--   2. its sum satisfies
--   $$\sum_{k\in\mathbb{N}^n}\eta(p_k)\;\le\;(n+1)\,\eta(q)+n\,q^2+N\,q .$$
--
--   The bound tends to $0$ as the mass $q$ tends to $0$ with the energy $N$ bounded, because $\eta(q)\to 0$. It therefore controls the entropy contribution of a small, finite-energy part of a distribution, such as the part of a state's diagonal discarded by a photon-number cutoff.
--
--   **Formalization Note** $\eta$ is `Real.negMulLog`. The total mass $q$ is not assumed to be at most $1$; it is automatically nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L695-L751

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

theorem OAI.QuantumTrace.entropy_small_mass_bound {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) {q : ℝ} (hq : HasSum p q)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    Summable (fun k => Real.negMulLog (p k)) ∧
    (∑' k, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 +
        (∑' k, (∑ j, (k j : ℝ)) * p k) * q := by sorry
