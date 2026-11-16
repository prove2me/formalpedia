-- Prove2me | Theorems.Thm_KTCenter_Supplement_theorem_5_13
-- name    : KTCenter.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:43.594199+00:00
-- url     : https://prove2.me/theorems/eecc06a6-f0c4-46a1-86b0-b0ee377d81b5
-- title:
--   Theorem 5.13 — randomized simultaneous approximation within $\xi W$ with probability $\ge 4/5$ in polynomial time
-- statement:
--   Fix $K\in\mathbb N$, positive rationals $C_0,C_1$ and a rational $0<\xi<1$. Consider cost instances $I$ satisfying (7): variables $U$ with finite nonempty allowed-key sets $\mathcal P_v$ of size at most $K$, surrogate costs $\tilde C_i$ ($i\in[n]$) of the form (6), and $W\ge1$ with $Q_0\le C_0W$ and $\Lambda\le C_1W$. Write $\mathcal P(U)$ for the allowed assignments.
--
--   There is a randomized algorithm, running in time polynomial in the total binary encoding length of $I$ on every execution, that always returns some $p\in\mathcal P(U)$, and with probability at least $4/5$ over fair coins the returned $p$ satisfies
--
--   $$\max_{i\in[n]}\tilde C_i(p)\le\min_{a\in\mathcal P(U)}\max_{i\in[n]}\tilde C_i(a)+\xi W.\qquad(70)$$
--
--   This is the randomized simultaneous optimization (JointOptimization, Algorithm 9) on which the randomized PTAS (Theorem 5.1) rests; §6 derandomizes it (Theorem 6.1).
--
--   **Formalization Note** The algorithm is one Mathlib `Turing.TM2ComputableInPolyTime` machine reading the coin string, a separator and the binary encoding of $I$; the number of coins and the running time on every coin string are bounded by fixed polynomials of the encoding length. The output is the list of key indices of $p$. Algorithm 9's LP solver leaves the choice among optimal LP solutions open, so the statement is the guarantee its proof gives for Algorithm 9: such a randomized algorithm exists.
--
--   Differences from the source:
--
--   - reading: "JointOptimization (Algorithm 9) returns p … the algorithm runs in polynomial time … on every execution" → there exists a TM2 machine on (coin string, binary encoding of I) whose number of coins and running time on every coin string are polynomial in the encoding length, with this guarantee; reason: the paper names no machine and counts binary encoding length; Algorithm 9 leaves the LP solver's optimal solution open, so the guarantee is the content
--   - reading: "with probability at least 4/5" → the fraction of coin strings of the fixed length on which the output satisfies (70) is ≥ 4/5; reason: probability over fair coins, as in Remark 5.14, which already accounts for the finite-bit loss
--   - reading: "returns p ∈ P(U) satisfying (70) with probability at least 4/5" → the output is an allowed assignment on every coin string, and (70) holds with probability ≥ 4/5; reason: the stronger of the two readings, and the one Algorithm 9 satisfies (every branch returns an assignment in P(U))
--   - encoding: K, C₀, C₁, ξ fixed, 0 < ξ < 1 (input of Algorithm 9) → parameters quantified before the machine, not inputs; reason: this is what "for fixed" says
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 5.13, eq. (70), p.53 (PDF p.55); Algorithm 9, p.54 (PDF p.56); Remark 5.14, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_encCost
import Definitions.Def_KTCenter_Supplement_coinFrac

namespace KTCenter.Supplement

/-- **Theorem 5.13** (Simultaneous approximation), eq. (70), p.53 (PDF p.55).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** "For fixed `K, C₀, C₁, ξ`": they precede the machine and are not inputs;
`0 < ξ < 1` is the input condition of Algorithm 9 (p.54). The instances "in (7)" are the published
`CostInstance K C₀ C₁`. A randomized algorithm is one Mathlib `Turing.TM2ComputableInPolyTime`
machine reading `encPair encCost (I, b)`; the number of coins is `L(|encCost I|)` for a polynomial
`L`, and the running time on every coin string is at most `P(|encCost I|)` for a polynomial `P`.
The output is always the list of key indices of an allowed assignment `p ∈ 𝒫(U)`, and (70) holds on
at least `4/5` of the coin strings (`coinFrac`). Reading: the theorem names Algorithm 9, whose LP
solver leaves the choice among optimal LP solutions open; the statement is the guarantee its proof
establishes, the existence of such a randomized polynomial-time algorithm. -/
theorem theorem_5_13 (K : ℕ) (C₀ C₁ ξ : ℚ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) :
    ∃ alg : CostInstance K C₀ C₁ × List Bool → List ℕ,
      ∃ h : Turing.TM2ComputableInPolyTime (encPair encCost) encIdx alg,
      ∃ L P : Polynomial ℕ,
        ∀ I : CostInstance K C₀ C₁,
          (∀ b : Fin (L.eval (encCost I).length) → Bool,
            h.time.eval (encPair encCost (I, List.ofFn b)).length ≤ P.eval (encCost I).length ∧
            ∃ p : I.Assign, alg (I, List.ofFn b) = idxList p) ∧
          (4 / 5 : ℚ) ≤ coinFrac alg (L.eval (encCost I).length) I
            (fun out => ∃ p : I.Assign,
              out = idxList p ∧ I.maxCost p ≤ I.minMaxCost + ξ * I.W) := by sorry

end KTCenter.Supplement
