-- Prove2me | Theorems.Thm_GreedNorm_Supplement_theorem_1_4
-- name    : GreedNorm.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:54:06.717212+00:00
-- url     : https://prove2.me/theorems/ac5e9922-0bfc-459c-8c67-0cb8961fa116
-- title:
--   Theorem 1.4 — a deterministic $2\psi^2\ln n$-approximation for GLB with piecewise-linear loads (corrected: $\max\{1,\cdot\}$)
-- statement:
--   **Setting (§4.1).** GLB with piecewise-linear loads: $m\ge1$ machines, $n$ jobs, processing times $p_{ij}\ge0$, nondecreasing left-continuous piecewise-linear $f_i:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ given explicitly, and a monotone symmetric norm $g$ on $\mathbb R^m$. An assignment $\sigma$ has loads $\mathrm{load}_i(\sigma)=f_i\big(\sum_{j:\sigma(j)=i}p_{ij}\big)$ and cost $g(\mathrm{load}(\sigma))$; $\mathrm{OPT}$ is the least cost.
--
--   **Theorem.** Let $\psi>0$. There is a deterministic polynomial-time algorithm that, on every such instance with
--
--   $$
--   f_i(2x)\le\psi\,f_i(x)\qquad\text{for every machine } i \text{ and every } x\ge0,
--   $$
--
--   outputs an assignment $\sigma$ with
--
--   $$
--   g(\mathrm{load}(\sigma))\ \le\ \max\{1,\ 2\psi^2\ln n\}\cdot\mathrm{OPT}.
--   $$
--
--   Formally: one admissible program of the base oracle real RAM, fixed from $\psi$ only, halts within $C(n+m+\sum_iK_i+2)^k$ steps on every such instance and its output cells hold such a $\sigma$.
--
--   Li and Khuller [LK11] studied this problem for $g=\ell_1$; its study under monotone symmetric norms was proposed as an open problem in [DLR23], and the theorem covers loads satisfying the doubling condition.
--
--   **Formalization Note** Input: the piecewise-linear instance layout ($n,m,K_i$ in integer memory; $p$ and the pieces in real memory); $g$ is the outer oracle and $v\mapsto f_i(\sum_j v_j)$ the inner oracle. Output: integer cell $2+j$ holds $\sigma(j)$. $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: ratio 2ψ² ln n → ratio max{1, 2ψ² ln n}; reason: at n = 1 the printed ratio is 0; counterexample n = m = 1, p = 1, f_1(z) = z (ψ = 2), g = |·|: OPT = 1 and every assignment costs 1 > 0; for n ≥ 2 the two agree unless every f_i ≡ 0 on [0, ∞), where every cost is 0
--   - encoding: fi(2x) ≤ ψ fi(x) for every i and x → for every i and every x ≥ 0; reason: f_i is defined on ℝ≥0 only
--   - encoding: nondecreasing left-continuous piecewise-linear f_i : ℝ≥0 → ℝ≥0 → explicit PWL data, left-continuous by construction, with hypotheses MonotoneOn on [0, ∞) and nonnegativity on [0, ∞); reason: the algorithm must read f_i; every such function has this form
--   - encoding: there is a deterministic approximation → one admissible GreedNorm.Machine program, chosen from ψ before the instance, halting within C(n + m + Σ_i K_i + 2)^k steps with σ in its output cells; reason: deterministic polynomial time on the base machine model, as in the published Theorem 1.3; g is a value oracle
--   - encoding: m machines → 0 < m; reason: with m = 0 and n ≥ 1 no assignment exists, and OPT needs a nonempty set of assignments
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 1.4, p.2 (PDF 4); Corollary 4.7 and its proof, p.12 (PDF 14); §4.1, p.11 (PDF 13)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_glbCost
import Definitions.Def_GreedNorm_OPT
import Definitions.Def_GreedNorm_Machine
import Definitions.Def_GreedNorm_Supplement_PWL
import Definitions.Def_GreedNorm_Supplement_pwlNorm
import Definitions.Def_GreedNorm_Supplement_pwlInitState

namespace GreedNorm.Supplement

/-- **Theorem 1.4 (= Corollary 4.7): a deterministic `2ψ² ln n`-approximation for GLB with
piecewise-linear loads** (corrected: ratio `max{1, 2ψ² ln n}`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 1.4, p.2 (PDF 4), restated as Corollary 4.7 and proved on p.12 (PDF 14): "If there
exists ψ > 0 such that fi(2x) ≤ ψfi(x) for every i and x, then there is a deterministic
2ψ² ln n-approximation to GLB with piecewise-linear loads."

For every `ψ > 0` there are one admissible program `P` of `GreedNorm.Machine` and constants
`C, k` such that for every instance (`n` jobs, `m ≥ 1` machines, `p_{ij} ≥ 0`, explicit
piecewise-linear `f_i` that are nondecreasing and nonnegative on `[0, ∞)` and satisfy
`f_i(2x) ≤ ψ f_i(x)` for all `i` and `x ≥ 0`, a monotone symmetric norm `g`), the run of `P`
halts within `C (n + m + Σ_i K_i + 2)^k` steps with an assignment `σ` of cost
`g(load(σ)) ≤ max{1, 2ψ² ln n} · OPT`.

**Formalization Note** Input layout `Supplement.pwlInitState p D`; the inner oracle is
`Supplement.pwlNorm D` (`v ↦ f_i(Σ_j v_j)`, computable from the input), the outer oracle is `g`;
each oracle call is one step. Output: on halting, integer cell `2 + j` holds `σ(j)`. `ln` is
`Real.log`. The program may depend on `ψ`, never on the instance. The size `Σ_i K_i` counts
breakpoints. At `n = 1` the printed ratio `0` is false, hence `max{1, ·}`. -/
theorem theorem_1_4 (ψ : ℝ) (hψ : 0 < ψ) :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C k : ℕ,
      ∀ (n m : ℕ) (hm : 0 < m) (p : Fin m → Fin n → ℝ), (∀ i j, 0 ≤ p i j) →
      ∀ (D : Fin m → Supplement.PWL),
        (∀ i, MonotoneOn (D i).eval (Set.Ici 0)) →
        (∀ i (z : ℝ), 0 ≤ z → 0 ≤ (D i).eval z) →
        (∀ i (z : ℝ), 0 ≤ z → (D i).eval (2 * z) ≤ ψ * (D i).eval z) →
      ∀ (g : (Fin m → ℝ) → ℝ), SymNormLoad.IsMonotoneSymmetricNorm g →
        ∃ t : ℕ, t ≤ C * (n + m + ∑ i, (D i).K + 2) ^ k ∧
          (Machine.run P (Supplement.pwlNorm (n := n) D) g (Supplement.pwlInitState p D) t).halted = true ∧
          ∃ σ : Fin n → Fin m,
            (∀ j : Fin n,
              (Machine.run P (Supplement.pwlNorm (n := n) D) g (Supplement.pwlInitState p D) t).integerMemory
                (2 + (j : ℤ)) = ((σ j : ℕ) : ℤ)) ∧
            glbCost p (Supplement.pwlNorm (n := n) D) g σ ≤
              max 1 (2 * ψ ^ 2 * Real.log (n : ℝ)) * OPT hm p (Supplement.pwlNorm (n := n) D) g := by sorry

end GreedNorm.Supplement
