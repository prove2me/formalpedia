-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_theorem_5_1
-- name    : HamSimTradeoff.AncillaDepth.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:16.974499+00:00
-- url     : https://prove2.me/theorems/8acb3c15-6f7f-4cf7-a04d-cf23a1fd890f
-- title:
--   Theorem 5.1 — effective-support ancilla-query tradeoff 2^a ≥ Mτ²/(Mτ + 2K²_{ε/τ}(T − 1)), its Ω_r form, and 2^a ≥ |supp(λ)| when ε = 0
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Suppose the uniform error bound (1.17) holds. For $\tau>\varepsilon$, let $M_\tau=|\{j:\lambda_j\ge\tau\}|$. If $N\ge T(M_\tau+1)^2$, then
--   $$2^a\ge\frac{M_\tau^2}{M_\tau+2K_{\varepsilon/\tau}^2(T-1)},\qquad K_r=\frac r{1-\sqrt{r(2-r)}}+\sqrt{\frac{2r}{1-r}}.$$
--   For every fixed $r\in[0,1)$ there is $c_r>0$, chosen before all circuit parameters and coefficients, such that $\varepsilon\le r\tau$ implies
--   $$2^a\ge c_r\frac{M_\tau^2}{M_\tau+T}.$$
--   Finally, if $\varepsilon=0$ and $N\ge T(|\operatorname{supp}(\lambda)|+1)^2$, then $2^a\ge|\operatorname{supp}(\lambda)|$ for every query count, where $\operatorname{supp}(\lambda)=\{j:\lambda_j>0\}$. These are the explicit, asymptotic and exact clauses of the effective-support tradeoff. The paper writes Omega_r; Lean states a positive constant chosen from r before all remaining parameters.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
--   - reading: When ε = 0, 2^a ≥ |supp(λ)| for arbitrary T, under the theorem's assumption N ≥ T(M_τ+1)² with τ unspecified → ε = 0 and N ≥ T(|supp(λ)|+1)² imply |supp(λ)| ≤ 2^a; reason: with ε = 0 every τ ∈ (0, min_{j∈supp} λ_j] has M_τ = |supp(λ)|, so this is the theorem's own dimension assumption at that τ; 'arbitrary T' means the bound does not depend on T
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 23, Theorem 5.1

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_LCU
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem theorem_5_1 :
    (∀ L N : ℕ, 1 ≤ N → ∀ B : LCUCircuit L, ∀ lam : Fin L → ℝ,
      ProbabilityWeights lam → ∀ eps tau : ℝ, 0 ≤ eps → eps < tau →
      LCUApprox B N lam eps → B.T*((effectiveSupport lam tau).card+1)^2 ≤ N →
      (((effectiveSupport lam tau).card:ℝ)^2 /
        (((effectiveSupport lam tau).card:ℝ) + 2*(K (eps/tau))^2*((B.T:ℝ)-1))) ≤ (2:ℝ)^B.a) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 → ∃ c : ℝ, 0 < c ∧
      ∀ L N : ℕ, 1 ≤ N → ∀ B : LCUCircuit L, ∀ lam : Fin L → ℝ,
      ProbabilityWeights lam → ∀ eps tau : ℝ, 0 ≤ eps → eps < tau → eps ≤ r*tau →
      LCUApprox B N lam eps → B.T*((effectiveSupport lam tau).card+1)^2 ≤ N →
      c*((effectiveSupport lam tau).card:ℝ)^2 /
        (((effectiveSupport lam tau).card:ℝ) + B.T) ≤ (2:ℝ)^B.a) ∧
    (∀ L N : ℕ, 1 ≤ N → ∀ B : LCUCircuit L, ∀ lam : Fin L → ℝ,
      ProbabilityWeights lam → LCUApprox B N lam 0 →
      B.T*((support lam).card+1)^2 ≤ N → (support lam).card ≤ 2^B.a) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
