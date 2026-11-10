-- Prove2me | Theorems.Thm_GreedNorm_theorem_1_3
-- name    : GreedNorm.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:22.093129+00:00
-- url     : https://prove2.me/theorems/3c28b14b-f640-4c9d-a67b-58d472a5cbf8
-- title:
--   Theorem 1.3 — deterministic polynomial-time $3(1+\epsilon)\ln n$-approximation for GLB (corrected: ratio $\max\{1,3(1+\epsilon)\ln n\}$)
-- statement:
--   **Generalized Load Balancing** (GLB): $n$ jobs, $m\ge1$ machines, processing times $p_{ij}\ge0$, a monotone symmetric norm $f_i$ on $\mathbb R^n$ for each machine and a monotone symmetric norm $g$ on $\mathbb R^m$. The cost of an assignment $\sigma$ of jobs to machines is $g\bigl((f_i(p_i[\sigma]))_i\bigr)$, and $\mathrm{OPT}$ is the minimum cost.
--
--   For every $\epsilon>0$ there are a deterministic algorithm, namely an admissible program $P$ of the value-oracle real RAM, and constants $C,k\in\mathbb N$ such that on every GLB instance $P$ halts within $C(n+m+2)^k$ steps and outputs an assignment $\sigma$ with
--
--   $$
--   g(\mathrm{load}(\sigma))\ \le\ \max\{1,\ 3(1+\epsilon)\ln n\}\cdot\mathrm{OPT}.
--   $$
--
--   For $n\ge2$ the ratio is the paper's $3(1+\epsilon)\ln n$. The bound is within a constant factor of the $O(\log n)$ randomized guarantee of Deng, Li and Rabani, and GLB with $f_i=\ell_\infty$, $g=\ell_1$ contains Set Cover.
--
--   **Formalization Note** The algorithm accesses $f_i$ and $g$ only through the machine's two oracle instructions, at unit cost. Input layout `glbInitState p` (integer cells $0,1$ hold $n,m$; real address $i\cdot n+j$ holds $p_{ij}$); output: integer cell $2+j$ holds $\sigma(j)$ when the machine halts. The program depends on $\epsilon$ only.
--
--   Differences from the source:
--   - correction: approximation ratio 3(1 + ϵ) ln n → ratio max{1, 3(1 + ϵ) ln n}; reason: counterexample: n = 1, m = 1, p_11 = 1, f_1 = g = |·|; OPT = 1, while ratio 3(1 + ϵ) ln 1 = 0 demands cost ≤ 0 (checked in the sanity file); for n ≥ 2, 3 ln 2 > 1 so the ratio is unchanged
--   - encoding: a set M of m machines → 0 < m; reason: for m = 0 and n ≥ 1 no assignment exists and OPT is undefined
--   - reading: GLB admits a deterministic approximation → one admissible deterministic program of the value-oracle real RAM, fixed for the given ϵ, halting within C(n + m + 2)^k steps on every instance with the stated cost bound; reason: an approximation algorithm is polynomial-time (the abstract and the proof, via Lemma 2.4's polynomial-size enumeration); without a time bound brute force is exact; the norms have no finite description, so oracle access is the input model
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
--   - encoding: jobs J, machines M, ln n → Fin n, Fin m (0-based); input in glbInitState, output in integer cells 2 + j; Real.log; reason: Lean convention; the paper fixes no encoding
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 1.3, p.2 (PDF 4); proof in §3.3, p.9 (PDF 11)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_glbCost
import Definitions.Def_GreedNorm_OPT
import Definitions.Def_GreedNorm_Machine
import Definitions.Def_GreedNorm_glbInitState

namespace GreedNorm

/-- **Theorem 1.3: a deterministic polynomial-time `3(1+ϵ) ln n`-approximation for Generalized Load
Balancing** (corrected: ratio `max{1, 3(1+ϵ) ln n}`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 1.3, p.2 (PDF 4): "For every ϵ > 0, GLB admits a deterministic approximation of
3(1 + ϵ) ln n"; proof §3.3, p.9 (PDF 11).

For every `ϵ > 0` there are one admissible program `P` of the deterministic value-oracle real
RAM and constants `C, k` such that for every GLB instance (`n` jobs, `m ≥ 1` machines,
processing times `p_{ij} ≥ 0`, monotone symmetric norms `f_i` on `ℝ^n` and `g` on `ℝ^m`), the
run of `P` on the instance halts within `C (n + m + 2)^k` steps with an assignment `σ` of
generalized makespan
$$ g(\mathrm{load}(\sigma)) \le \max\{1,\ 3(1+\epsilon)\ln n\}\cdot \mathrm{OPT}. $$

**Formalization Note** Jobs `Fin n`, machines `Fin m` (0-based). Input layout: `glbInitState p`
(integer cells `0, 1` hold `n, m`; real cell `i·n + j` holds `p i j`); the norms are reachable
only through the oracle instructions, each call costing one step. Output: on halting, integer
cell `2 + j` holds `σ(j)`. `ln` is `Real.log`. The program may depend on `ϵ`, never on the
instance. The ratio is the one in the statement of Theorem 1.3 and in the first sentence of §3.3;
Table 1, p.3 (PDF 5), lists "(2 + ϵ) ln n" and the last sentence of §3.3 says "(3 + ϵ)-approximation",
both inconsistent with the theorem and its proof (Theorem 3.2 with `α = 1`). -/
theorem theorem_1_3 (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C k : ℕ,
      ∀ (n m : ℕ) (hm : 0 < m) (p : Fin m → Fin n → ℝ), (∀ i j, 0 ≤ p i j) →
      ∀ (f : Fin m → (Fin n → ℝ) → ℝ), (∀ i, SymNormLoad.IsMonotoneSymmetricNorm (f i)) →
      ∀ (g : (Fin m → ℝ) → ℝ), SymNormLoad.IsMonotoneSymmetricNorm g →
        ∃ t : ℕ, t ≤ C * (n + m + 2) ^ k ∧
          (Machine.run P f g (glbInitState p) t).halted = true ∧
          ∃ σ : Fin n → Fin m,
            (∀ j : Fin n,
              (Machine.run P f g (glbInitState p) t).integerMemory (2 + (j : ℤ)) = ((σ j : ℕ) : ℤ)) ∧
            glbCost p f g σ ≤ max 1 (3 * (1 + ε) * Real.log (n : ℝ)) * OPT hm p f g := by sorry

end GreedNorm
