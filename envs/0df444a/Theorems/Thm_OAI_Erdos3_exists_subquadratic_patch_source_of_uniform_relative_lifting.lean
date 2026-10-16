-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_subquadratic_patch_source_of_uniform_relative_lifting
-- name    : OAI.Erdos3.exists_subquadratic_patch_source_of_uniform_relative_lifting
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:57:44.80723+00:00
-- url     : https://prove2.me/theorems/8a8c8adb-5ac2-4121-9118-c74911e73274
-- title:
--   Uniform relative patch lifting rules give a subquadratic patch source
-- statement:
--   Let $s$ and $n_0$ be natural numbers with $n_0 \ne 0$ and $s \ge 1$. Suppose that for every real $\tau$ with $0 < \tau \le 1/2$ there is a natural number $E \ge 2$ with `RelativePatchPowerInductionRule s n₀ s τ E` (OpenAI's `RelativePatchInductionRule s n₀ s τ cutoff cost` with $\mathrm{cutoff}(p) = \mathrm{cost}(p) = (p+2)^E$: a proposition asserting that, under stated size, density, progression-freeness and patch-score hypotheses, `RelativePatchSliceConclusion` holds). Then there exist reals $\kappa, H_0, K, B, D, p_{\min}$ with $\kappa > 0$, $\kappa H_0 > 1$, $K \ge 2$, $B > 0$, $D > 0$ and `SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (log 2)`.
--
--   Here `SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc` is the following proposition. Put $\mu = \mathrm{levelCoefficient}(K) \log q$ and $\beta = 1 - (\mathrm{gainExponent}(K) - \mu)/2$, where `levelCoefficient K` $= 1/(4 \log K)$ and `gainExponent K` $= \mathrm{levelCoefficient}(K) \log 2$. For every `APFreeInterval k` $S$ (a length $\ell > 1$ and a nonempty set $A_S \subseteq \{0, \dots, \ell-1\}$ with no $k$-term arithmetic progression; its density is $\alpha = |A_S|/\ell$ and its parameter is $\pi = \max(2, \log(2/\alpha))$) with $p_{\min} \le \pi$ and $A_0 \pi^\beta + C_{\mathrm{src}} \le \log\log \ell$, there exist natural numbers $d, M, a, q_0$, a real $U$ and a `PolynomialPatch Unit s d` $A$ (a structure of weights in $[1,s]$, polynomial slots, and a kernel with Lipschitz constant $A.\mathrm{kernel.lip}$; $A.\mathrm{value}$ is its real value) such that $q_0 > 0$; $a + q_0 n < \ell$ for all $n < M$; $U \ge 1$; $\log \ell - U \le \log M$; $A.\mathrm{kernel.lip} + 1 \le e^U$; $\log(d+1) \le B \pi^\mu \log(2 + \pi)$; $\log U \le D \pi^{1/4} \log(2 + \pi)$; and, with $G = \kappa \cdot \mathrm{amplificationGain}(\kappa, H_0, \lfloor \mathrm{levelCoefficient}(K) \log \pi \rfloor)/2$,
--   $$e^{-U} \le \mathop{\mathbb E}_{n \in \mathrm{Fin}\,M} \bigl(\mathbf 1_{A_S}(a + q_0 n) - G\alpha\bigr)\, A.\mathrm{value}(n),$$
--   where `amplificationGain κ H₀` is the sequence $g_0 = H_0$, $g_{j+1} = \kappa g_j^2$.
--
--   Lean: `OAI.Erdos3.exists_subquadratic_patch_source_of_uniform_relative_lifting` in `lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1342` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean#L499

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1342

namespace OAI

section

open Filter
open scoped Topology

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open Filter

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem exists_subquadratic_patch_source_of_uniform_relative_lifting
    (s n₀ : ℕ) [NeZero n₀] (hs : 1 ≤ s)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule s n₀ s τ E) :
    ∃ κ H₀ K B D pmin : ℝ,
      0 < κ ∧ 1 < κ * H₀ ∧ 2 ≤ K ∧ 0 < B ∧ 0 < D ∧
      SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (Real.log 2) := by
  sorry

end Erdos3
end
end OAI
