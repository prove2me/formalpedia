-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_2_19
-- name    : LosslessQLTC.lemma_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:25.677+00:00
-- url     : https://prove2.me/theorems/e94860c2-3665-46db-b9d1-3c1b2991d21b
-- title:
--   Lemma 2.19, pp.19–20 — excess, edge and large-degree bounds for a lossless bigraph
-- statement:
--   Let $H=(L,R,E)$ be a one-sided $(c,\varepsilon)$-lossless $(D,D')$-biregular bigraph.
--
--   1. (Excess bound.) If $A\subseteq L$ satisfies $|A|\le c|L|$, then $\sum_{y\in R}(\deg_A(y)-1)_+=D|A|-|\Gamma(A)|\le\varepsilon D|A|$.
--   2. (Lossless edge bound.) If $A\subseteq L$ satisfies $|A|\le c|L|$, then for every $B\subseteq R$, $e(A,B)\le|B|+\varepsilon D|A|$.
--   3. (Large-degree bound.) For $B\subseteq R$, if at most $c|L|$ vertices $x\in L$ satisfy $\deg_B(x)>\varepsilon D$, then
--
--   $$\sum_{x\in L}\Big(\frac{\deg_B(x)}{D}-\varepsilon\Big)_+\le\frac{|B|}{D}.$$
--
--   These three bounds are how lossless expansion enters the counts of Section 4.
--
--   Differences from the source: none.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 2.19, pp.19–20

import Mathlib
import Definitions.Def_LosslessQLTC_Bigraph

namespace LosslessQLTC

/-- Lemma 2.19 (arXiv:2610.00525, held version, sha256 d61f0ed9…, pp.19–20): for a one-sided
`(c, ε)`-lossless `(D, D′)`-biregular bigraph `H = (L, R, E)`,
1. if `|A| ≤ c|L|` then `Σ_{y ∈ R} (deg_A(y) − 1)_+ = D|A| − |Γ(A)| ≤ εD|A|`;
2. if `|A| ≤ c|L|` then `e(A, B) ≤ |B| + εD|A|` for every `B ⊆ R`;
3. if at most `c|L|` vertices `x ∈ L` have `deg_B(x) > εD`, then
   `Σ_{x ∈ L} (deg_B(x)/D − ε)_+ ≤ |B|/D`.

**Formalization Note.** `t_+` is `max t 0`. -/
theorem lemma_2_19 {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : L → R → Prop) [DecidableRel E] (D D' : ℕ) (c ε : ℝ)
    (hbi : IsBiregular E D D') (hl : IsOneSidedLossless E D c ε) :
    (∀ A : Finset L, (A.card : ℝ) ≤ c * Fintype.card L →
      (∑ y : R, max ((degLeft E A y : ℝ) - 1) 0) = (D : ℝ) * A.card - (nbhd E A).card ∧
      (D : ℝ) * A.card - (nbhd E A).card ≤ ε * D * A.card) ∧
    (∀ A : Finset L, (A.card : ℝ) ≤ c * Fintype.card L → ∀ B : Finset R,
      (edgeCount E A B : ℝ) ≤ B.card + ε * D * A.card) ∧
    (∀ B : Finset R,
      (((Finset.univ : Finset L).filter fun x => ε * D < (degRight E B x : ℝ)).card : ℝ) ≤
          c * Fintype.card L →
        (∑ x : L, max ((degRight E B x : ℝ) / D - ε) 0) ≤ (B.card : ℝ) / D) := by sorry

end LosslessQLTC
