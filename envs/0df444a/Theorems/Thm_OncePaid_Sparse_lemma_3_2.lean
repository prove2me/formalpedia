-- Prove2me | Theorems.Thm_OncePaid_Sparse_lemma_3_2
-- name    : OncePaid.Sparse.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:37.394819+00:00
-- url     : https://prove2.me/theorems/a356b89a-7b24-476b-bac0-ff3a1b594cfc
-- title:
--   Lemma 3.2 — probe budget $s+O\le b$, matching deficit $\le b$, coupled prices keep optimum $3n$, $\|D_M(F)\|_1\le 2(F(3)-3n)$
-- statement:
--   Let $H=(V_L\cup V_R,E)$ be a bipartite host with a perfect matching $M:V_L\to V_R$, so that both sides have $n$ vertices, and let $f_H$ be either minimum-weight perfect matching or full minimum-weight edge cover. For an affine form $P(c)=\beta(P)+\sum_e\alpha_e(P)c_e$ write $P(3)$ for its value at the all-three table, $p^M$ for the matching probe (3 on $M$, 4 elsewhere), and $M_{<1}=\{e\in M:\alpha_e(P)<1\}$.
--
--   1. **Probe budget (3.1).** Let $P$ have nonnegative price coefficients, be sound ($P\ge f_H$) at the all-three table and at the subset test with price 4 on $M_{<1}$ and off $M$ and price 3 on $M\setminus M_{<1}$, and satisfy $P(p^M)\le 3n+b$ with $b\ge0$. With $s=P(3)-3n$ and $O=\sum_{e\notin M}\alpha_e(P)$,
--
--   $$
--   s\ge0,\qquad s+O\le b,\qquad \sum_{e\in M}\big(1-\alpha_e(P)\big)_+\le b .
--   $$
--
--   2. **Coupled prices (3.2).** For every $v\in\{-1,1\}^{V_L}$ the prices $c_{ij}=3+\tfrac12\big(v_i-v_{M^{-1}(j)}\big)$, $ij\in E$, have optimum $f_H(c)=3n$, for both objectives.
--   3. **Imbalance (3.3).** Every affine form $F$ that is sound at all coupled prices (3.2) obeys $\|D_M(F)\|_1\le 2\big(F(3)-3n\big)$, where $D_M(F)_i=r_i(F)-q_{M(i)}(F)$ and $r_i,q_j$ are the row and column coefficient totals.
--
--   These inequalities let a near-optimal parse at a matching probe pay for its off-matching mass and its row/column imbalance out of one budget $b$.
--
--   Differences from the source:
--   - reading: "sound at the tests below" → part 1 assumes soundness only at the all-three table and at the subset test raising $M_{<1}$; part 3 assumes soundness at all coupled tests (these include the all-three table, $v$ constant); reason: the strongest reading, exactly the tests the page's argument uses.
--   - encoding: $H$ with $n$ vertices on each side and at least one perfect matching → arbitrary finite sides with the perfect matching $M$ given, $n=|V_L|$; objective values in `WithTop ℝ`; reason: $|V_R|=n$ follows from the bijection $M$; Lean convention for $+\infty$.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 13, Lemma 3.2, Eqs. (3.1)–(3.3) (PDF p. 15)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Parse
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- Lemma 3.2 (Probe budget and coupled prices), p. 13. `H` is a bipartite host with a perfect
matching `M` (so `|V_L| = |V_R| = n`), and `obj` is either objective.
(3.1): an affine form `P` with nonnegative coefficients, sound at the all-three table and at the
subset test raising `M_{<1} = {e ∈ M : α_e(P) < 1}` to four, with `P(p^M) ≤ 3n + b`, `b ≥ 0`,
has `s ≥ 0`, `s + O ≤ b` and `Σ_{e ∈ M} (1 − α_e(P))₊ ≤ b`, where `s = P(3) − 3n` and
`O = Σ_{e ∉ M} α_e(P)`.
(3.2): for every `v ∈ {−1, 1}^{V_L}` the coupled prices have optimum `3n`.
(3.3): every affine form `F` sound at all coupled tests has `‖D_M(F)‖₁ ≤ 2 (F(3) − 3n)`. -/
theorem lemma_3_2 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop) (obj : Objective)
    (M : L ≃ R) (hM : IsPerfectMatching adj M) :
    (∀ (P : AffineForm (Edge adj)) (b : ℝ), P.NonnegCoef → 0 ≤ b →
      objValue adj obj (uniformPrices adj 3) ≤ ((P.eval (uniformPrices adj 3) : ℝ) : WithTop ℝ) →
      objValue adj obj (subsetTest M {e | P.coef e < 1}) ≤
        ((P.eval (subsetTest M {e | P.coef e < 1}) : ℝ) : WithTop ℝ) →
      P.eval (probe M) ≤ 3 * (Fintype.card L : ℝ) + b →
      0 ≤ P.eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ) ∧
      P.eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ) + offMass M P ≤ b ∧
      matchDeficit M P ≤ b) ∧
    (∀ v : L → ℝ, IsSignVector v →
      objValue adj obj (coupledPrices M v) = ((3 * (Fintype.card L : ℝ) : ℝ) : WithTop ℝ)) ∧
    (∀ F : AffineForm (Edge adj), SoundAtCoupled adj obj M F →
      imbalance M F ≤ 2 * (F.eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ))) := by sorry

end OncePaid.Sparse
