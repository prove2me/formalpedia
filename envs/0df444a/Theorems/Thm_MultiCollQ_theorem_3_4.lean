-- Prove2me | Theorems.Thm_MultiCollQ_theorem_3_4
-- name    : MultiCollQ.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:34.359529+00:00
-- url     : https://prove2.me/theorems/f7dd95c7-1180-4539-a77f-11ee4aa59a01
-- title:
--   Theorem 3.4 — $A_j\le(8k)^{1-2^{1-j}}$, $A_j=c_j\sqrt{A_{j-1}}$, $\sup_{s\le T}m_j(s)\le A_j\lambda_j$, $a_{j,1}(T)\le\min\{1,A_j\lambda_j\}$
-- statement:
--   For $1\le j\le k$ let $A_j=\prod_{i=2}^{j}(8(k-i+1))^{2^{i-j-1}}$ (empty product $1$). Then:
--
--   1. $A_j\le(8k)^{1-2^{1-j}}$;
--   2. $A_1=1$ and $A_j=c_j\sqrt{A_{j-1}}$ for $2\le j\le k$;
--   3. for public buckets of sizes at most $k$, every forward compressed-query algorithm, every integer $1\le T<N$ and every $1\le j\le k$, with $\lambda_j=T^{\alpha_j}/(N-T)^{\beta_j}$,
--   $$
--   \sup_{0\le s\le T}m_j(s)\le A_j\lambda_j,\qquad a_{j,1}(T)\le\min\{1,A_j\lambda_j\};
--   $$
--   4. for $2\le r\le k$ and $T\le N/2$ (with $1\le T<N$),
--   $$
--   a_{r,1}(T)\le\frac{(16k)^{1-2^{1-r}}\,T^{2-2^{1-r}}}{N^{1-2^{1-r}}}.
--   $$
--
--   Clause 4 is the single $r$-collision bound: a database bucket with $r$ images needs $T=\Omega_{k,r}(N^{\beta_r/\alpha_r})$ queries.
--
--   **Formalization Note** Real powers throughout.
--
--   Differences from the source:
--   - encoding: $\sup_{0\le s\le T}m_j(s)\le A_j\lambda_j$ → $m_j(s)\le A_j\lambda_j$ for every $s\le T$; reason: same statement
--   - encoding: $T\le N/2$ → `2 * T ≤ N`; reason: same condition in natural numbers
--   - encoding: $a_{r,1}(T)\le(16k)^{1-2^{1-r}}T^{2-2^{1-r}}/N^{1-2^{1-r}}=O_{k,r}(T^{2-2^{1-r}}/N^{1-2^{1-r}})$ for fixed $k,r$ → the explicit inequality, for $2\le r\le k$; reason: the $O_{k,r}$ form follows from the explicit constant; $2\le r\le k$ is the range fixed at the start of §3
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `FwdAlg` and its compressed state; reason: same class of algorithms
--   - encoding: $[N]$ and the buckets $Q_1,\dots,Q_h$ with $d_b\le k$ (§3, p.18) → `Fin N` (0-based) and a bucket map `b : Fin N → Fin h` with `BucketsBounded b k` (sizes in $[1,k]$); reason: Lean convention; blocks of a partition are nonempty; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Theorem 3.4, (3.14), p.25

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg

namespace MultiCollQ

open CompPermOracle

/-- Theorem 3.4 (Single-target bounds of every order without truncation) (Peng, Hou, Dong,
manuscript (Oct. 2026), p.25). For `1 ≤ j ≤ k`, `A_j = ∏_{i=2}^{j} (8(k − i + 1))^{2^{i−j−1}}`
satisfies:
1. `A_j ≤ (8k)^{1−2^{1−j}}`;
2. `A_1 = 1` and `A_j = c_j √A_{j−1}` for `2 ≤ j ≤ k`;
3. for buckets of sizes at most `k`, every forward compressed-query algorithm, every integer
   `1 ≤ T < N` and every `1 ≤ j ≤ k`: `sup_{0≤s≤T} m_j(s) ≤ A_j λ_j` and
   `a_{j,1}(T) ≤ min{1, A_j λ_j}` (3.14), `λ_j = T^{α_j}/(N − T)^{β_j}`;
4. for `2 ≤ r ≤ k` and `T ≤ N/2` (with `1 ≤ T < N`):
   `a_{r,1}(T) ≤ (16k)^{1−2^{1−r}} T^{2−2^{1−r}} / N^{1−2^{1−r}}`.

**Formalization Note.** The supremum over `0 ≤ s ≤ T` is the bound for every `s ≤ T`. `T ≤ N/2` is
`2T ≤ N`. The `O_{k,r}(·)` of the "in particular" clause is implied by the explicit constant
`(16k)^{1−2^{1−r}}`, which is what is stated. Real powers throughout. -/
theorem theorem_3_4 (k : ℕ) :
    (∀ j, 1 ≤ j → j ≤ k → Aconst k j ≤ (8 * (k : ℝ)) ^ (1 - (2 : ℝ) ^ (1 - (j : ℝ)))) ∧
    Aconst k 1 = 1 ∧
    (∀ j, 2 ≤ j → j ≤ k → Aconst k j = cConst k j * Real.sqrt (Aconst k (j - 1))) ∧
    (∀ {N h T : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk] (b : Fin N → Fin h),
      BucketsBounded b k → ∀ A : FwdAlg N Wk, 1 ≤ T → T < N → ∀ j, 1 ≤ j → j ≤ k →
        (∀ s ≤ T, firstMoment b j (A.compressedState s) ≤ Aconst k j * lambdaScale N T j) ∧
        dbAmp b j 1 (A.compressedState T) ≤ min 1 (Aconst k j * lambdaScale N T j)) ∧
    (∀ {N h T r : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk] (b : Fin N → Fin h),
      BucketsBounded b k → ∀ A : FwdAlg N Wk, 2 ≤ r → r ≤ k → 1 ≤ T → T < N → 2 * T ≤ N →
        dbAmp b r 1 (A.compressedState T) ≤
          (16 * (k : ℝ)) ^ (1 - (2 : ℝ) ^ (1 - (r : ℝ))) * (T : ℝ) ^ (2 - (2 : ℝ) ^ (1 - (r : ℝ))) /
            (N : ℝ) ^ (1 - (2 : ℝ) ^ (1 - (r : ℝ)))) := by sorry

end MultiCollQ
