-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_theorem_1_8
-- name    : MongeApprox.Sparsify.theorem_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:03:12.722605+00:00
-- url     : https://prove2.me/theorems/4d903cc7-2031-47d9-a8a5-bc0c62860c77
-- title:
--   Theorem 1.8 — every normalized Monge matrix has a (1+ε)-approximation with core Õ(n log W/√ε), computed in Õ(n log W/√ε) time
-- statement:
--   There are constants $C>0$, $c\in\mathbb N$ and one admissible program $P$ such that the following holds. Consider a parameter $\varepsilon\in(0,1]$ and a normalized Monge matrix $M$ with dimensions at most $n$ and entries in $\{0\}\cup[1,W]$ for some $W\ge2$. There is a Monge matrix $\widehat M$ such that $M_{ij}\le\widehat M_{ij}\le(1+\varepsilon)M_{ij}$ holds entrywise, and the core of $\widehat M$ has size at most $C\cdot\frac{n\log W}{\sqrt\varepsilon}\cdot\log^c(n+2)$. If $M$ is integer-valued, then so is $\widehat M$. Furthermore, given $p,q,\varepsilon$ and oracle access to the entries of $M$ (not $W$), $P$ halts within $C\cdot\frac{n\log W}{\sqrt\varepsilon}\cdot\log^c(n+2)$ steps and outputs the condensed representation of this $\widehat M$.
--
--   Differences from the source:
--   - generalization: word RAM with Ω(log N)-bit words extended with real registers (§3 Model of Computation, p. 18 / PDF 20) → the mission's `Program` on `SmaleNinth` core + integer ±, integer memory, int→real cast, `entry`, `halt`; rational literals only; no integer ×/÷/bit operations; reason: fewer operations and literals than the paper's machine, so an existence claim over these programs is stronger and implies the source's
--   - reading: word RAM with machine words of Ω(log N) bits, a lower bound on the word length only (§3 Model of Computation, p. 18 / PDF 20) → integer registers and integer memory cells hold unbounded integers (ℤ); every register and every memory cell not holding input is initially 0; reason: the paper bounds the word length only from below and leaves the initial memory content unspecified; zero-initialized memory is the usual RAM convention
--   - encoding: Õ(n log(W)/√ε) (polylogarithmic factors in the input size suppressed, footnote 1) → C·(n log W/√ε)·(log(n+2))^c with C > 0, c ∈ ℕ and P chosen before n, p, q, ε, W, M; reason: the standing reading of Õ with size parameter n; uniform constants
--   - encoding: given oracle access to the entries of M → input: integer cells p, q and real cell ε; `entry` oracle for M; W is not an input; reason: a declared input layout
--   - encoding: the condensed representation of M̂ → `OutputsCondensed`: top row, leftmost column, core size and exactly the nonzero density triples in declared output cells; reason: a declared output layout
--   - encoding: a matrix (implicitly with at least one row and one column) → hypotheses 1 ≤ p, 1 ≤ q; reason: only excludes empty matrices, for which M_00 and the condensed representation are undefined
--   - encoding: log (base unspecified, inside O(·)) → `Real.log` (natural logarithm); reason: inside O(·) the base changes only the constant C
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Theorem 1.8, printed p. 5 (PDF 7); proof via Theorem 7.3, printed p. 35 (PDF 37)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Machine

namespace MongeApprox.Sparsify

/-- Theorem 1.8 (Monge matrix approximation). There are constants `C > 0`, `c ∈ ℕ` and one
admissible program `P` such that for every `ε ∈ (0, 1]`, every `W ≥ 2`, every `n` and every Monge
`p × q` matrix `M` with `1 ≤ p, q ≤ n` and entries in `{0} ∪ [1, W]`, there is a Monge matrix `M̂`
with `M_ij ≤ M̂_ij ≤ (1 + ε) M_ij` entrywise, core size `δ(M̂) ≤ C · (n log W/√ε) · (log(n + 2))^c`,
integer-valued if `M` is, and `P`, given `p`, `q`, `ε` and oracle access to the entries of `M`
(not `W`), halts within `C · (n log W/√ε) · (log(n + 2))^c` steps with the condensed
representation of this `M̂` as output. -/
theorem theorem_1_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (n p q : ℕ) (M : Matrix (Fin p) (Fin q) ℝ) (ε W : ℝ),
        1 ≤ p → p ≤ n → 1 ≤ q → q ≤ n → 0 < ε → ε ≤ 1 → 2 ≤ W →
        IsMonge M → (∀ i j, M i j = 0 ∨ (1 ≤ M i j ∧ M i j ≤ W)) →
        ∃ Mhat : Matrix (Fin p) (Fin q) ℝ,
          IsMonge Mhat ∧
          (∀ i j, M i j ≤ Mhat i j ∧ Mhat i j ≤ (1 + ε) * M i j) ∧
          (coreSize Mhat : ℝ) ≤
            C * ((n : ℝ) * Real.log W / Real.sqrt ε) * Real.log ((n : ℝ) + 2) ^ c ∧
          (IsIntegerValued M → IsIntegerValued Mhat) ∧
          HaltsWithin P M (init [(p : ℤ), (q : ℤ)] [ε])
            (C * ((n : ℝ) * Real.log W / Real.sqrt ε) * Real.log ((n : ℝ) + 2) ^ c)
            (OutputsCondensed Mhat) := by sorry

end MongeApprox.Sparsify
