-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_theorem_7_3
-- name    : MongeApprox.Sparsify.theorem_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:51.987373+00:00
-- url     : https://prove2.me/theorems/216b1a5a-282e-4b8c-a98c-c24c4ddf40a9
-- title:
--   Theorem 7.3 — Monge matrix sparsification with threshold K: κ preserved, core and time O(H)
-- statement:
--   There are $C>0$ and an admissible program $P$ such that the following holds. Consider a normalized nonnegative Monge matrix $M$ with dimensions at most $n\ge2$ and parameters $K\in[0,+\infty]$ and $\varepsilon\in(0,1]$. Let $H:=\frac{n}{\sqrt\varepsilon}\log n\cdot\log(2+\min\{K,\kappa(M)\})$. There is a normalized nonnegative Monge matrix $\widehat M$ with $\delta(\widehat M)\le CH$ and $\kappa(\widehat M)=\kappa(M)$ that $(1+\varepsilon,K)$-approximates $M$. If $M$ is integer-valued, then so is $\widehat M$. Given $p,q,\varepsilon,K$ and oracle access to the entries of $M$, $P$ halts within $CH$ steps (entry queries and additional work) and outputs the condensed representation of this $\widehat M$.
--
--   Differences from the source:
--   - generalization: word RAM with Ω(log N)-bit words extended with real registers (§3 Model of Computation, p. 18 / PDF 20) → the mission's `Program` on `SmaleNinth` core + integer ±, integer memory, int→real cast, `entry`, `halt`; rational literals only; no integer ×/÷/bit operations; reason: fewer operations and literals than the paper's machine, so an existence claim over these programs is stronger and implies the source's
--   - reading: word RAM with machine words of Ω(log N) bits, a lower bound on the word length only (§3 Model of Computation, p. 18 / PDF 20) → integer registers and integer memory cells hold unbounded integers (ℤ); every register and every memory cell not holding input is initially 0; reason: the paper bounds the word length only from below and leaves the initial memory content unspecified; zero-initialized memory is the usual RAM convention
--   - encoding: O(H) core size; O(H) entry queries and additional work → ∃ C > 0 fixed before every instance: δ(M̂) ≤ C·H and halting within C·H steps (every instruction counted); reason: explicit constant for O(·)
--   - encoding: the parameters K ∈ [0, +∞] and ε are given to the algorithm → input: integer cells p, q and a flag (1 iff K = +∞); real cells ε and K (K.toReal, 0 when K = +∞); reason: a declared input layout; +∞ cannot be stored in a real register
--   - encoding: the condensed representation of M̂ → `OutputsCondensed`: top row, leftmost column, core size and exactly the nonzero density triples in declared output cells; reason: a declared output layout
--   - encoding: a matrix (implicitly with at least one row and one column) → hypotheses 1 ≤ p, 1 ≤ q; reason: only excludes empty matrices, for which M_00 and the condensed representation are undefined
--   - encoding: log (base unspecified, inside O(·)) → `Real.log` (natural logarithm); reason: inside O(·) the base changes only the constant C
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Theorem 7.3, printed p. 35 (PDF 37); proof printed pp. 38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Machine

namespace MongeApprox.Sparsify

open scoped ENNReal

/-- Theorem 7.3 (Monge matrix sparsification). There are `C > 0` and an admissible program `P`
such that for every `n ≥ 2`, every normalized nonnegative Monge `p × q` matrix `M` with
`1 ≤ p, q ≤ n`, every `K ∈ [0, +∞]` and every `ε ∈ (0, 1]`, with
`H := (n/√ε) · log n · log(2 + min{K, κ(M)})`, there is a normalized nonnegative Monge matrix `M̂`
with `δ(M̂) ≤ C · H` and `κ(M̂) = κ(M)` that `(1 + ε, K)`-approximates `M`, integer-valued if `M`
is; and `P`, given `p`, `q`, `ε`, `K` (as a flag for `K = +∞` and the real `K` otherwise) and
oracle access to the entries of `M`, halts within `C · H` steps with the condensed representation
of this `M̂` as output. -/
theorem theorem_7_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (n p q : ℕ) (M : Matrix (Fin p) (Fin q) ℝ) (K : ℝ≥0∞) (ε : ℝ),
        2 ≤ n → 1 ≤ p → p ≤ n → 1 ≤ q → q ≤ n → 0 < ε → ε ≤ 1 →
        IsNonneg M → IsNormalized M → IsMonge M →
        ∃ Mhat : Matrix (Fin p) (Fin q) ℝ,
          IsNonneg Mhat ∧ IsNormalized Mhat ∧ IsMonge Mhat ∧
          (coreSize Mhat : ℝ) ≤
            C * ((n : ℝ) / Real.sqrt ε * Real.log n *
              Real.log (2 + minThreshold K (totalCurvature M))) ∧
          totalCurvature Mhat = totalCurvature M ∧
          Approximates (1 + ε) K M Mhat ∧
          (IsIntegerValued M → IsIntegerValued Mhat) ∧
          HaltsWithin P M
            (init [(p : ℤ), (q : ℤ), if K = ⊤ then 1 else 0] [ε, K.toReal])
            (C * ((n : ℝ) / Real.sqrt ε * Real.log n *
              Real.log (2 + minThreshold K (totalCurvature M))))
            (OutputsCondensed Mhat) := by sorry

end MongeApprox.Sparsify
