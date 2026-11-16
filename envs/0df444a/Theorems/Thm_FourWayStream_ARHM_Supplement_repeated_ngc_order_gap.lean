-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_repeated_ngc_order_gap
-- name    : FourWayStream.ARHM.Supplement.repeated_ngc_order_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:11:49.30325+00:00
-- url     : https://prove2.me/theorems/8777c0f5-a085-4542-9b15-376f368c77c1
-- title:
--   Theorem 7.11 — order gap for repeated NGC: $O(h\log n)$ walkers in random order versus $\Omega(n)$ quantum space in clustered order
-- statement:
--   Let $(n,k)$ be admissible.
--   1. Run $h\ge0$ walkers from independent uniform starts and answer "$k$-cycles" if some walker returns after exactly $k$ steps. On an $R$-repeated stream ($R\ge1$) in uniformly random order this algorithm has one-sided error: it never errs on $2k$-cycle instances, and on $k$-cycle instances it errs with probability at most
--   $$2^{-h}+\mathbb P[\mathrm{Pois}(R)<k].$$
--   It uses $O(h\log n)$ classical bits, with a universal constant. For $h=5$ and $R\ge2k$ the error is below $1/4$.
--   2. If a quantum algorithm with space $S$ solves $\mathrm{NGC}_{n,k}$ on $R$-repeated streams in uniformly clustered order with error $1/3$, then some single-arrival quantum algorithm solves $\mathrm{NGC}_{n,k}$ in uniformly random order with error $1/3$ in space $S+O(\log n+\log R)$; so $S+O(\log n+\log R)$ is at least the single-arrival random-order space. If $k\ge1600\log_2n$ (and $n$ is large), this is $\Omega(n)$ by Theorem 7.3.
--
--   So for $k\ge1600\log_2n$ and $R=2k$, the same multiset of $R\,|E|=2kn-n$ items ($\Theta(n\log n)$ items when $k=\Theta(\log n)$) needs $O(\log n)$ classical bits in random order and $\Omega(n)$ quantum space in clustered order.
--
--   **Formalization Note** The $O$, $\Omega$ constants and the size threshold are universal, quantified before $n,k,h,R$ and the algorithms. Part 2's lower bound is stated for every $R\ge1$ as $cn\le S+C(\log_2n+\log_2R)$; $S=\Omega(n)$ is concluded only for $R=2k$. For $h=0$ the algorithm always answers "$2k$-cycles", stores nothing, and the error bound is $1$. The walker counters stop at $2k$, as the paper allows.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators → every item is processed by an arbitrary quantum instrument (finite complete Kraus family) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels ("they only use that the memory between two items is a state of the given number of qubits and bits"); this is the base mission's reading
--   - generalization: §4.2: a step may depend on the stage only through stored memory; space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - encoding: (n, k) admissible: k ≥ 3 and 4k ∣ n (n = 0 allowed by the printed definition) → 0 < n in the clauses that assert validity of the walker algorithm and the error below 1/4 for h = 5; reason: for n = 0 both cases of Definition 7.1 are the empty graph, so the problem is undefined; the condition only excludes this case
--   - encoding: uses O(h log n) classical bits; S + O(log n + log R) is at least the single-arrival random-order space → space ≤ C·h·log₂ n and the existence of a single-arrival random-order algorithm with error ≤ 1/3 and space ≤ S + C(log₂ n + log₂ R), for universal C; the simulation preserves stage independence; reason: the meaning of the O-bounds with universal constants; the minimum-space statement is the existence of the simulating algorithm
--   - generalization: the final separation for k = Θ(log n) with k ≥ 1600 log n and R = 2k → every admissible (n, k) with n ≥ n₀ and k ≥ 1600 log₂ n, R = 2k; the item count is the exact identity R·|E| = 2kn − n; reason: the upper bound k = O(log n) is not needed for either space bound; it is needed only to read 2kn − n as Θ(n log n), which the exact identity gives
--   - encoding: a walker stores a step counter ℓ → the walkers of the algorithm store the counter stopped at 2k (min ℓ 2k); reason: on an NGC instance a walker closes after k or 2k steps or never, and moves at most k − 1 times on a path, so the cap changes no decision
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.37, Theorem 7.11 (proof pp.37–38, Appendix E, pp.49–50)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_Walker

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.11 (Order gap for repeated NGC), p.37 (proof pp.37–38). Let `(n, k)` be admissible (with `n > 0` where the
problem must be nondegenerate: for `n = 0` both cases of Definition 7.1 are the empty graph).
1. The algorithm running `h ≥ 0` walkers from independent uniform starts and answering "`k`-cycles"
   iff some walker returns after exactly `k` steps has, on `R`-repeated streams in uniformly random
   order (`R ≥ 1`), one-sided error: it never errs on `2k`-cycle instances and errs on `k`-cycle
   instances with probability at most `2^{−h} + P[Pois(R) < k]`; it is a valid stage-independent
   classical algorithm using at most `C h log₂ n` bits for a universal `C`; for `h = 5` and `R ≥ 2k`
   its error is below `1/4`.
2. If a quantum algorithm with space `S` solves `NGC_{n,k}` on `R`-repeated streams in uniformly
   clustered order with error `1/3`, then some single-arrival random-order quantum algorithm with
   error `1/3` uses at most `S + C(log₂ n + log₂ R)` space (universal `C`), so `S + O(log n + log R)`
   is at least the single-arrival random-order space; if `k ≥ 1600 log₂ n` (and `n` is large), this is
   `Ω(n)`.
So for `k ≥ 1600 log₂ n` and `R = 2k`, the same multiset of `2kn − n` items (`Θ(n log n)` when
`k = Θ(log n)`) needs `O(log n)` classical bits in random order and `Ω(n)` quantum space in clustered
order. -/
theorem repeated_ngc_order_gap :
    (∀ n k h R : ℕ, Admissible n k → 1 ≤ R → ∀ E : Finset (Sym2 (Fin n)),
      (IsNGC n k true E →
        avgRepRandOrder E R (fun str => (walkerAlg n k h).accept str false) = 0) ∧
      (IsNGC n k false E →
        avgRepRandOrder E R (fun str => (walkerAlg n k h).accept str true) ≤
          (2 : ℝ) ^ (-(h : ℤ)) + poissonLT R k)) ∧
    (∀ n k h : ℕ, Admissible n k → 0 < n →
      (walkerAlg n k h).Valid ∧ (walkerAlg n k h).StageIndependent) ∧
    (∃ C : ℝ, ∀ n k h : ℕ, Admissible n k →
      ((walkerAlg n k h).space : ℝ) ≤ C * h * Real.logb 2 n) ∧
    (∀ n k R : ℕ, Admissible n k → 0 < n → 2 * k ≤ R → ∀ (long : Bool) (E : Finset (Sym2 (Fin n))),
      IsNGC n k long E →
        1 - avgRepRandOrder E R (fun str => (walkerAlg n k 5).accept str long) < 1 / 4) ∧
    (∃ C : ℝ, ∀ n k R : ℕ, Admissible n k → 1 ≤ R → ∀ A : QEdgeAlg (Fin n), A.Valid →
      A.ClusteredErrorLE k R (1 / 3) →
        ∃ A' : QEdgeAlg (Fin n), A'.Valid ∧ A'.RandErrorLE k (1 / 3) ∧
          (A'.space : ℝ) ≤ A.space + C * (Real.logb 2 n + Real.logb 2 R) ∧
          (A.StageIndependent → A'.StageIndependent)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n k R : ℕ, Admissible n k → n₀ ≤ n →
      1600 * Real.logb 2 n ≤ k → 1 ≤ R → ∀ A : QEdgeAlg (Fin n), A.Valid →
        A.ClusteredErrorLE k R (1 / 3) → c * n ≤ A.space + C * (Real.logb 2 n + Real.logb 2 R)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n k : ℕ, Admissible n k → n₀ ≤ n →
      1600 * Real.logb 2 n ≤ k →
        (∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E →
          E.card * (2 * k) = 2 * k * n - n ∧
          1 - avgRepRandOrder E (2 * k) (fun str => (walkerAlg n k 5).accept str long) < 1 / 4) ∧
        ((walkerAlg n k 5).space : ℝ) ≤ C * Real.logb 2 n ∧
        ∀ A : QEdgeAlg (Fin n), A.Valid → A.ClusteredErrorLE k (2 * k) (1 / 3) →
          c * n ≤ A.space) := by sorry

end FourWayStream.ARHM.Supplement
