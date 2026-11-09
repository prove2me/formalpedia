-- Prove2me | Theorems.Thm_HybridXorLift_theorem_5_3
-- name    : HybridXorLift.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:13.358191+00:00
-- url     : https://prove2.me/theorems/1a777b53-cc82-442f-85e3-85c8feab0f5f
-- title:
--   Theorem 5.3 — transcript simulation with $\lfloor 100T/r\rfloor$ outer queries within total variation $0.002$
-- statement:
--   Let $n \ge 0$, $r \ge 1$ and $q \ge 1$ be integers with $r \ge 100\, q \ln(n + 2)$. For every parallel $q$-query hybrid algorithm $A$ of cost $T$ on $nr$ physical bits there is a classical randomized algorithm that makes at most $\lfloor 100T/r\rfloor$ queries to an outer string $z \in \{0,1\}^n$ and outputs a terminal transcript of $A$ or the symbol $\bot$, such that for every $z$
--   $$
--   \big\| \mathcal L(\text{output on } z) - \mathcal L_{x \sim \sigma^{-1}(z)}(\text{terminal transcript of } A \text{ on } x) \big\|_{\mathrm{TV}} \le 0.002 ,
--   $$
--   where $x$ is uniform on the parity fibre $\sigma^{-1}(z)$.
--
--   The information a parallel hybrid algorithm obtains about the outer bits is essentially no more than what a classical algorithm with a $100/r$ fraction of its queries can obtain.
--
--   **Formalization Note** The classical algorithm is a randomized decision tree on $\{0,1\}^n$ (a distribution over deterministic trees, each making at most $\lfloor 100T/r\rfloor$ queries on every input) whose outputs are terminal histories of $A$ or $\bot$. The terminal transcript of $A$ on $x$ has law $\lambda \mapsto |c_\lambda(x)|^2$, and its law on the fibre is the fibre average, extended by $0$ at $\bot$.
--
--   Differences from the source:
--   - encoding: a subroutine starts from an input-independent (possibly mixed) state and ends with an arbitrary measurement → a pure unit start state on query register(s) × workspace Fin w, input-independent unitaries, and a complete computational-basis measurement with one child per outcome; reason: §2.2: purifying every preparation and dilating every measurement change neither the cost nor the output distribution, so the class of algorithms is the paper's
--   - encoding: physical bits x_ij with i ∈ [n], j ∈ [r], bits in {0,1} → functions Fin n × Fin r → Bool, 0-based block and position; reason: Lean convention; same instances
--   - encoding: a terminal transcript: the original measurement outcomes along a root-to-leaf path, before the refinement of §2.2 → a terminal history of the (already refined) tree, as a list of complete measurement outcomes; reason: the model is refined, and a bound for the refined transcript implies the bound for the original one since a deterministic map does not increase total variation
--   - encoding: a classical randomized algorithm with at most ⌊100T/r⌋ queries outputting a transcript or ⊥ → a randomized decision tree (PMF over decision trees) with RandMakesAtMost (100 * T / r) and outputs in Option of the terminal histories, none = ⊥; reason: the paper's randomized decision tree model (§2.1)
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Theorem 5.3, p.19 (PDF p.21)

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_HybridXorLift_fibreAvg
import Definitions.Def_HybridXorLift_pathProb
import Definitions.Def_HybridXorLift_ParallelHybridAlg_terminals
import Definitions.Def_HybridXorLift_ParallelHybridAlg_cost
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Theorem 5.3 (Transcript simulation) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.19 (PDF p.21). Let `n ≥ 0`, `r ≥ 1` and
`q ≥ 1` be integers with `r ≥ 100 q ln(n + 2)`. For every parallel `q`-query hybrid algorithm `A`
of cost `T` on `nr` physical bits there is a classical randomized algorithm that makes at most
`⌊100T/r⌋` queries to an outer string `z ∈ {0,1}ⁿ` and outputs a terminal transcript of `A` or
`⊥`; for every `z`, its output distribution is within total variation distance `0.002` of the
distribution of the terminal transcript of `A` on a uniformly random input from `σ⁻¹(z)`.

**Formalization Note** The classical algorithm is a randomized decision tree (a distribution over
deterministic decision trees, each making at most `100 * T / r` queries on every outer string)
with outputs in `Option` of the terminal histories, `none` being `⊥`. The terminal transcript of
`A` on `x` has law `λ ↦ |c_λ(x)|²` (`pathProb`); its law on a uniform `x ∈ σ⁻¹(z)` is the fibre
average, extended by `0` at `⊥`. The model is already refined (§2.2), so the terminal transcript
is the list of complete measurement outcomes along the root-to-leaf path. -/
theorem theorem_5_3 {n r q : ℕ} {α : Type} (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hrq : 100 * (q : ℝ) * Real.log ((n : ℝ) + 2) ≤ r)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q) :
    ∃ R : QAlgorithms.RandDecisionTree (Fin n) Bool (Option {l // l ∈ A.terminals}),
      QAlgorithms.RandMakesAtMost R (100 * A.cost / r) ∧
      ∀ z : Fin n → Bool,
        tvDist (fun o => QAlgorithms.successProb R z o)
          (fun o => o.elim 0 fun l => fibreAvg z fun x => pathProb A x l.1) ≤ 0.002 := by sorry

end HybridXorLift
