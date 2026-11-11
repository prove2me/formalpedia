-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_lemma_2_11
-- name    : LowRankShifts.MatPoly.lemma_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:09.786421+00:00
-- url     : https://prove2.me/theorems/e3c5e3be-b74f-4adc-a487-4c30ff9f55dc
-- title:
--   Lemma 2.11 — self-correction of a degree-d polynomial map from a (1 − 2^{−d}/10)-correct oracle with 2^{d+1} − 1 queries
-- statement:
--   Let $F$ be a finite field and $f:F^\ell\to F^m$ a map each of whose $m$ entries is a polynomial of degree at most $d$ in the $\ell$ coordinates. There is a universal constant $C$ and, for each $F,\ell,m$, one program $B$ of the machine `LowRankShifts_MatPoly_Machine` taking as input a vector $x\in F^\ell$ and the degree bound $d$, such that for every such $f$, every $x$ and every (possibly randomized, memoryless) oracle $O:F^\ell\to F^m$: every run halts after at most $C\,2^d(m+\ell)+C$ operations and exactly $2^{d+1}-1$ queries, and
--
--   $$\Pr_{a\sim F^\ell}[O(a)=f(a)]\ \ge\ 1-\frac{2^{-d}}{10}\quad\Longrightarrow\quad \Pr[B(x)=f(x)]\ \ge\ \frac45 ,$$
--
--   the left probability over a uniform $a$ and the oracle's randomness, the right one over $B$'s samples and the oracle's answers.
--
--   It is the basic worst-case to average-case reduction for low-degree maps: an oracle that is correct on all but a $2^{-d}/10$ fraction of inputs is turned into an algorithm correct on every input with probability $4/5$.
--
--   **Formalization Note.** $x$ occupies field cells $0,\dots,\ell-1$ and $d$ index register $0$ (`vectorInput`); the output is the $m$ cells from the address designated by `haltOut`. Probabilities are read from the run law after the step budget (`finalLaw`, `probOut`). The statement is posed as printed; at $\ell=m=0$ its time bound is $C$, while $B$, which receives $d$ as input, must make $2^{d+1}-1$ queries, so it is false there (see the mission's insights).
--
--   Differences from the source:
--   - encoding: a randomized (oracle) algorithm whose time is its number of field operations (p. 8) → a `Program` of the machine `LowRankShifts_MatPoly_Machine` (field operations, index operations without multiplication or field↔index conversion, a vector oracle); time = the `ops` counter, queries = the `queries` counter; `sample` draws from the uniform law on the field; reason: the paper names no machine; this one charges every field and index operation one unit and cannot pack a matrix into one integer
--   - encoding: input x ∈ F^ℓ and a degree bound d; output f(x) ∈ F^m → x in field cells 0, …, ℓ−1 and d in index register 0 (`vectorInput d x`); the output is the m cells from the address designated by `haltOut`; reason: a fixed input/output convention of the machine
--   - encoding: a (possibly randomized) oracle C : F^ℓ → F^m → a memoryless PMF-valued oracle, every query an independent draw from the law of its answer; reason: the paper's oracles answer each query with fresh randomness (proof of Theorem 3.5, p. 21); a deterministic oracle is the case of point masses
--   - encoding: each entry of f is a polynomial of degree at most d → for every j there is `q : MvPolynomial (Fin ℓ) F` with `q.totalDegree ≤ d` and `f y j = eval y q` for all y; reason: the same condition, stated with Mathlib's polynomials
--   - reading: runs in time O(2^d(m + ℓ)) → every run halts with ops ≤ C·2^d·(m + ℓ) + C, the constant fixed before every other quantity (field, polynomial, dimensions, inputs, oracle); reason: worst-case reading of O(·) as C·f + C on every run; time counts field operations at unit cost (p. 8), so the constant does not depend on the field
--   - reading: makes 2^{d+1} − 1 queries → every run makes at most and exactly 2^{d+1} − 1 queries; reason: the count is stated as an exact number; the algorithm queries every nonempty S ⊆ [d+1]
--   - generalization: Fix f; there is an algorithm B taking x and d → one program B for each F, ℓ, m that works for every d and every f of degree at most d; reason: B receives d as input and does not read f; a program for each fixed f is the special case
--   - encoding: Pr[B(·) = ·] over the algorithm's coins and the oracle's answers → `probOut` of the run law after the step budget (`finalLaw`): the probability that the run halts with `haltOut` and the designated output equals the target; ⊥ (`halt`) counts as failure; reason: all runs halt within the budget (first conjunct), so this is the probability over complete runs
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 13 (PDF 16), Lemma 2.11

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

set_option autoImplicit false

universe u

namespace LowRankShifts.MatPoly

/-- Lemma 2.11 (p. 13): one program `B` (for the field `F` and the dimensions `ℓ`, `m`) that, on
input `x ∈ F^ℓ` and a degree bound `d`, for every `f : F^ℓ → F^m` whose entries are polynomials
of degree at most `d` and every (possibly randomized, memoryless) oracle `O : F^ℓ → F^m`, halts on
every run within `C·2^d·(m + ℓ) + C` operations after exactly `2^{d+1} − 1` queries, and outputs
`f(x)` with probability at least `4/5` whenever `Pr_{a ∼ F^ℓ}[O(a) = f(a)] ≥ 1 − 2^{−d}/10`. -/
theorem lemma_2_11 :
    ∃ C : ℝ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (ℓ m : ℕ),
      ∃ B : Program F, ∀ (d : ℕ) (f : (Fin ℓ → F) → (Fin m → F)),
        (∀ j : Fin m, ∃ q : MvPolynomial (Fin ℓ) F,
          q.totalDegree ≤ d ∧ ∀ y : Fin ℓ → F, f y j = MvPolynomial.eval y q) →
        ∀ (O : VecOracle F ℓ m) (x : Fin ℓ → F),
          let T : ℝ := C * 2 ^ d * ((m : ℝ) + ℓ) + C
          let Q : ℝ := 2 ^ (d + 1) - 1
          RunsWithin (PMF.uniformOfFintype F) O B (vectorInput d x) T Q ∧
          (∀ σ ∈ (finalLaw (PMF.uniformOfFintype F) O B (vectorInput d x) T Q).support,
            σ.queries = 2 ^ (d + 1) - 1) ∧
          (1 - (2 : ℝ) ^ (-(d : ℤ)) / 10 ≤
              ZamirInversion581.Mult.unifMean (fun y : Fin ℓ → F => (O y (f y)).toReal) →
            4 / 5 ≤ probOut (finalLaw (PMF.uniformOfFintype F) O B (vectorInput d x) T Q)
              (outVec m) (some (f x))) := by sorry

end LowRankShifts.MatPoly
