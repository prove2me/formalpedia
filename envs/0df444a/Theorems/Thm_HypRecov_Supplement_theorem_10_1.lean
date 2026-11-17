-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_10_1
-- name    : HypRecov.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:28:48.638658+00:00
-- url     : https://prove2.me/theorems/d607a9d8-df39-4817-9503-729f82cede68
-- title:
--   Theorem 10.1 — exact output-information lower bound
-- statement:
--   Set $c=\lceil3n/4\rceil$ and $N_r=\binom{c}{r-1}$. If $1\le k-1\le N_r$, every randomized final-state scheme that recovers $\mathcal B_k(H)$ with probability at least $2/3$ for every simple $r$-uniform input requires
--   $$(n-c)\log_2\binom{N_r}{k-1}+\log_2(2/3)$$
--   bits in the worst case.
--
--   There is also one absolute constant $\gamma>0$ such that, when $n\ge8$, $2\le r\le n/2$, and $k-1\le\sqrt{N_r}$, every such scheme uses at least
--   $$\gamma nkr\log_2(n/r)$$
--   bits.
--
--   Differences from the source:
--   - encoding: arbitrary public, encoder and randomized-decoder coins and an $s$-bit final state → one finite nonempty uniform random tape shared by encoder and decoder and state type `Fin (2^s)`; reason: the proof fixes all random tapes together, and every distribution generated from finitely many random bits has this form
--   - encoding: $\Omega(nkr\log(n/r))$ → an absolute $\gamma>0$ quantified before $n,r,k$ and the recovery scheme; reason: this is the standard uniform meaning of the asymptotic clause
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 10.1 and proof, pp.27-28 (PDF pp.28-29)

import Mathlib
import Definitions.Def_HypRecov_Supplement_FinalRecoveryScheme

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem 10.1 (Output-information lower bound).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 10.1,
p.27 (PDF p.28).

Let `c=ceil(3n/4)` and `N_r=choose c (r-1)`.  Every randomized `s`-bit final-state scheme that
recovers `B_k(H)` with probability at least `2/3` on every simple `r`-uniform input satisfies the
exact logarithmic bound.  In the printed parameter range it also satisfies the asymptotic lower
bound with one absolute positive constant chosen before `n,r,k` and the scheme.

**Formalization Note.** Encoder, public, and decoder randomness are one finite uniform tape in
`FinalRecoveryScheme`; fixing that tape is exactly the counting argument in the proof.  The state
type is `Fin (2^s)`. -/
theorem theorem_10_1 :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ (n r k s : ℕ) (A : FinalRecoveryScheme n r k s),
        2 ≤ r → r ≤ n →
        let c := threeQuarterCeil n
        let Nr := c.choose (r - 1)
        1 ≤ k - 1 → k - 1 ≤ Nr → FinalRecovers A →
          informationLowerBound n r k ≤ (s : ℝ) ∧
          (8 ≤ n → 2 * r ≤ n → (k - 1 : ℝ) ≤ Real.sqrt Nr →
            gamma * n * k * r * Real.logb 2 (n / r : ℝ) ≤ s)
    := by sorry

end HypRecov.Supplement
