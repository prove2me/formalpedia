-- Prove2me | Theorems.Thm_HybridXorLift_theorem_1_1
-- name    : HybridXorLift.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:42.697874+00:00
-- url     : https://prove2.me/theorems/79464b91-ecee-44f7-a61b-5177cbcaa002
-- title:
--   Theorem 1.1 — one-query XOR lifting: $Q(f\circ\mathrm{XOR}_r; 1) \ge r\,R(f)/2500$ for $r \ge 100\ln(n+2)$
-- statement:
--   Let $f : D \to \{0,1\}$ be a partial Boolean function with $D \subseteq \{0,1\}^n$. For every integer $r \ge 100 \ln(n + 2)$,
--   $$
--   Q(f \circ \mathrm{XOR}_r;\, 1) \ \ge\ \frac{r\, R(f)}{2500} .
--   $$
--   Here $Q(g;1)$ is the least cost of a one-query hybrid algorithm (Definition 2.1) computing $g$ with error at most $1/3$ on every promised input, with the input accessed through the controlled phase oracle, and $R(f)$ is the bounded-error randomized query complexity of $f$.
--
--   The bound is tight up to a constant factor, since a one-query hybrid algorithm can run a randomized decision tree for $f$ and read all $r$ bits of a block whenever it needs a parity, so $Q(f \circ \mathrm{XOR}_r;1) \le r R(f)$. On parity-encoded inputs, one-query hybrid algorithms cannot asymptotically beat this classical strategy.
--
--   **Formalization Note** The statement covers every $n$ (including $n = 0$) and every partial $f$ (including empty and constant ones, where $R(f) = 0$). $R(f)$ is the published `NoPerfectRandComp.R`; $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: a subroutine starts from an input-independent (possibly mixed) state and ends with an arbitrary measurement → a pure unit start state on query register(s) × workspace Fin w, input-independent unitaries, and a complete computational-basis measurement with one child per outcome; reason: §2.2: purifying every preparation and dilating every measurement change neither the cost nor the output distribution, so the class of algorithms is the paper's
--   - encoding: error at most 1/3 on every promised input → probability at least 2/3 of outputting the correct bit on every promised input; reason: the outputs are bits, whose probabilities sum to one
--   - encoding: physical bits x_ij with i ∈ [n], j ∈ [r], bits in {0,1} → functions Fin n × Fin r → Bool, 0-based block and position; reason: Lean convention; same instances
--   - encoding: Q(g;1) as the least cost → sInf over ℕ of the admissible costs (hybridQ); reason: the set of admissible costs is nonempty for finite index sets, so the infimum is the least cost
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Theorem 1.1, p.2 (PDF p.4)

import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_HybridXorLift_xorComp
import Definitions.Def_HybridXorLift_hybridQ

namespace HybridXorLift

/-- Theorem 1.1 (One-query XOR lifting) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.2 (PDF p.4). Let `f : D → {0,1}` be a
partial Boolean function with `D ⊆ {0,1}ⁿ`. For every integer `r ≥ 100 ln(n + 2)`,
`Q(f ∘ XOR_r; 1) ≥ r R(f) / 2500`.

**Formalization Note** `R(f)` is the published `NoPerfectRandComp.R` and `Q(·; 1)` is `hybridQ · 1`
over `HybridAlg` (Definition 2.1 in the refined form of §2.2), with the controlled phase oracle
(2.1) on the physical bits `Fin n × Fin r`. `ln` is `Real.log`. Every `n` (including `0`) and
every partial `f` (including an empty or constant one) is covered. -/
theorem theorem_1_1 {n : ℕ} (f : NoPerfectRandComp.PartialFn (Fin n)) (r : ℕ)
    (hr : 100 * Real.log ((n : ℝ) + 2) ≤ r) :
    (r : ℝ) * (NoPerfectRandComp.R f : ℝ) / 2500 ≤ (hybridQ (xorComp f r) 1 : ℝ) := by sorry

end HybridXorLift
