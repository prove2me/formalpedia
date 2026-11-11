-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_fact_7_4
-- name    : MongeApprox.Sparsify.fact_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:03:00.857705+00:00
-- url     : https://prove2.me/theorems/753edfb3-3063-4042-a3f2-11e87e4c91d7
-- title:
--   Fact 7.4 — nonnegative Monge = potentials + simple F + transposed-simple G with disjoint supports, constructed with O(n) queries
-- statement:
--   There are $C>0$ and admissible programs (a setup program and query programs for $F$ and $G$) such that every nonnegative Monge $p\times q$ matrix $M$ with $1\le p,q\le n$ can be written $M_{ij}=r_i+c_j+F_{ij}+G_{ij}$ with $r_i,c_j\ge0$, $F$ and $G^\top$ simple Monge matrices, and disjoint entrywise supports of $F$ and $G$ (for each $(i,j)$, $F_{ij}=0$ or $G_{ij}=0$). Furthermore, with oracle access to the entries of $M$, the setup program halts within $C n$ steps (entry queries and additional work), outputting the row potentials and column potentials; from its halted state, the query program for $F$ (resp. $G$), started with $(i,j)$, halts within $C$ steps with at most one entry query and returns $F_{ij}$ (resp. $G_{ij}$) in real register $0$.
--
--   Differences from the source:
--   - generalization: word RAM with Ω(log N)-bit words extended with real registers (§3 Model of Computation, p. 18 / PDF 20) → the mission's `Program` on `SmaleNinth` core + integer ±, integer memory, int→real cast, `entry`, `halt`; rational literals only; no integer ×/÷/bit operations; reason: fewer operations and literals than the paper's machine, so an existence claim over these programs is stronger and implies the source's
--   - reading: word RAM with machine words of Ω(log N) bits, a lower bound on the word length only (§3 Model of Computation, p. 18 / PDF 20) → integer registers and integer memory cells hold unbounded integers (ℤ); every register and every memory cell not holding input is initially 0; reason: the paper bounds the word length only from below and leaves the initial memory content unspecified; zero-initialized memory is the usual RAM convention
--   - encoding: oracles for the entries of F and G constructed from M's oracle; a query requires one query to M and constant additional work → query programs PF, PG run from the setup program's halted state (`queryState s i j`, memories kept, i and j in pointer registers 0 and 1) halt within C steps with at most one entry query and the entry in real register 0; every query starts from the same setup state; reason: an oracle is a data structure plus a query procedure; starting each query from the same state models a read-only structure and changes no instance
--   - encoding: O(n) oracle queries and additional work → the setup program halts within C·n steps, every step (oracle calls included) counted, C fixed before n, p, q, M; reason: explicit constant for O(·), uniform over all instances
--   - encoding: the row and column potentials are constructed → real outputs 0..p−1 hold r_i and p..p+q−1 hold c_j at halt; reason: a declared output layout
--   - encoding: M with dimensions at most n → 1 ≤ p ≤ n, 1 ≤ q ≤ n; reason: only excludes empty matrices
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Fact 7.4, printed p. 35 (PDF 37); cited from [RW95] and [GK25, Appendix A.1]

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Machine

namespace MongeApprox.Sparsify

/-- Fact 7.4 (Monge matrix decomposition). There are a constant `C > 0` and three admissible
programs (a setup program and entry-query programs for `F` and for `G`) such that every
nonnegative Monge `p × q` matrix `M` with `1 ≤ p, q ≤ n` is `M_ij = r_i + c_j + F_ij + G_ij` with
`r_i, c_j ≥ 0`, `F` and `Gᵀ` simple Monge, and disjoint entrywise supports of `F` and `G`; with
oracle access to `M`, the setup program halts within `C · n` steps and outputs the row potentials
(real outputs `0, …, p − 1`) and column potentials (real outputs `p, …, p + q − 1`), and from its
halted state each entry `F_ij` (resp. `G_ij`) is computed into real register `0` within `C` steps
using at most one entry query. -/
theorem fact_7_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ Psetup PF PG : Program,
      Admissible Psetup ∧ Admissible PF ∧ Admissible PG ∧
      ∀ (n p q : ℕ) (M : Matrix (Fin p) (Fin q) ℝ),
        1 ≤ p → p ≤ n → 1 ≤ q → q ≤ n → IsNonneg M → IsMonge M →
        ∃ (r : Fin p → ℝ) (c : Fin q → ℝ) (F G : Matrix (Fin p) (Fin q) ℝ),
          (∀ i j, M i j = r i + c j + F i j + G i j) ∧
          (∀ i, 0 ≤ r i) ∧ (∀ j, 0 ≤ c j) ∧
          IsSimple F ∧ IsSimple G.transpose ∧
          (∀ i j, F i j = 0 ∨ G i j = 0) ∧
          HaltsWithin Psetup M (init [(p : ℤ), (q : ℤ)] []) (C * n) (fun s =>
            (∀ i : Fin p, realOut s i = r i) ∧
            (∀ j : Fin q, realOut s (p + j) = c j) ∧
            (∀ (i : Fin p) (j : Fin q),
              HaltsWithin PF M (queryState s i j) C
                (fun s' => s'.queries ≤ 1 ∧ s'.core.regs 0 = F i j)) ∧
            (∀ (i : Fin p) (j : Fin q),
              HaltsWithin PG M (queryState s i j) C
                (fun s' => s'.queries ≤ 1 ∧ s'.core.regs 0 = G i j))) := by sorry

end MongeApprox.Sparsify
