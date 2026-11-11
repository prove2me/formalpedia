-- Prove2me | Theorems.Thm_OncePaid_Sparse_lemma_3_3
-- name    : OncePaid.Sparse.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:42.581724+00:00
-- url     : https://prove2.me/theorems/b3a1e211-2470-4bca-9ac7-3239290fb71d
-- title:
--   Lemma 3.3 — a single budget pays for the cut: $X_{U^*,V}(M)\le(2s'+2O_{\mathrm{out}}+O_{\mathrm{in}})/\kappa$, one $V$ per group
-- statement:
--   Let $H$ be a bipartite host with $n$ vertices on each side, let $\kappa>0$, and fix $U^*\subseteq V_L$, $V^*\subseteq V_R$. Then there is one set $V\subseteq V_R$ with $|V|=|U^*|$ such that the following holds for every objective $f_H$ (perfect matching or full edge cover), every perfect matching $M$, every $b$, and all affine forms $R_{\mathrm{out}},Q,Q'$ in the edge prices with nonnegative price coefficients. Put $P=R_{\mathrm{out}}+Q$ and $P'=R_{\mathrm{out}}+Q'$, and assume:
--
--   1. $P(p^M)\le 3n+b$ and $P$ satisfies the budget (3.1): $s\ge0$, $s+O\le b$, $\sum_{e\in M}(1-\alpha_e(P))_+\le b$, with $s=P(3)-3n$, $O=\sum_{e\notin M}\alpha_e(P)$;
--   2. $P$ and $P'$ are sound at all coupled tests (3.2);
--   3. $|U(Q)|=|U(Q')|$ and $|V(Q)|=|V(Q')|$ (row and column support cardinalities);
--   4. every nonzero price coefficient of $Q$ and of $Q'$ is at least $\kappa$;
--   5. $U(Q')=U^*$ and $V(Q')=V^*$.
--
--   Then, with $s'=P'(3)-3n$, $O_{\mathrm{out}}=\sum_{e\notin M}\alpha_e(R_{\mathrm{out}})$ and $O_{\mathrm{in}}=\sum_{e\notin M}\alpha_e(Q)$,
--
--   $$
--   X_{U^*,V}(M)=|M(U^*)\,\triangle\,V|\ \le\ \frac{2s'+2O_{\mathrm{out}}+O_{\mathrm{in}}}{\kappa}. \tag{3.4}
--   $$
--
--   This is the single-lemma form of both sentences of Lemma 3.3: the existence of $V$, and the use of the same $V$ throughout a group in which the supports of $Q'$ and their cardinalities are fixed.
--
--   Differences from the source:
--   - generalization: $P=R_{\mathrm{out}}+Q$ a parse and $P'=R_{\mathrm{out}}+Q'$ a valid output parse → arbitrary affine forms $R_{\mathrm{out}},Q,Q'$ with nonnegative coefficients; reason: the conclusion uses only the stated properties of the forms, and the forms of parses are such forms, so the statement specializes to the source's.
--   - reading: "there is a set V … If the supports of Q′ and their cardinalities are fixed in a group, the same V can be used throughout that group" → one statement: for fixed $U^*,V^*$ one $V$ serves every matching, form, budget and objective whose $Q'$ has supports $U^*,V^*$; reason: this is the group clause, and a single parse is a group of one.
--   - encoding: $n$ vertices on each side → hypothesis $|V_R|=|V_L|$, $n=|V_L|$; reason: the standing assumption of §3.2.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 14, Lemma 3.3, Eq. (3.4) (PDF p. 16)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Parse
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- Lemma 3.3 (A single budget pays for the cut), p. 14, in its group-uniform form. Let `H` have
`n` vertices on each side, fix `κ > 0` and supports `U* ⊆ V_L`, `V* ⊆ V_R`. There is one
`V ⊆ V_R` with `|V| = |U*|` such that for every perfect matching `M`, every objective, and all
affine forms `R_out, Q, Q'` with nonnegative coefficients satisfying: `P = R_out + Q` has
`P(p^M) ≤ 3n + b` and the budget (3.1); `P` and `P' = R_out + Q'` are sound at the coupled tests
(3.2); `Q, Q'` have the same row and the same column support cardinalities; every nonzero
coefficient of `Q` and of `Q'` is at least `κ`; and `U(Q') = U*`, `V(Q') = V*` — one has
`X_{U*,V}(M) ≤ (2s' + 2O_out + O_in)/κ` (3.4), where `s' = P'(3) − 3n`,
`O_out = Σ_{e ∉ M} α_e(R_out)`, `O_in = Σ_{e ∉ M} α_e(Q)`. -/
theorem lemma_3_3 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (κ : ℝ) (hκ : 0 < κ)
    (Ustar : Finset L) (Vstar : Finset R) :
    ∃ V : Finset R, V.card = Ustar.card ∧
      ∀ (obj : Objective) (M : L ≃ R) (Rout Q Q' : AffineForm (Edge adj)) (b : ℝ),
        IsPerfectMatching adj M →
        Rout.NonnegCoef → Q.NonnegCoef → Q'.NonnegCoef →
        (Rout + Q).eval (probe M) ≤ 3 * (Fintype.card L : ℝ) + b →
        0 ≤ (Rout + Q).eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ) →
        (Rout + Q).eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ) +
          offMass M (Rout + Q) ≤ b →
        matchDeficit M (Rout + Q) ≤ b →
        SoundAtCoupled adj obj M (Rout + Q) →
        SoundAtCoupled adj obj M (Rout + Q') →
        (rowSupport Q).card = (rowSupport Q').card →
        (colSupport Q).card = (colSupport Q').card →
        (∀ e, Q.coef e ≠ 0 → κ ≤ Q.coef e) →
        (∀ e, Q'.coef e ≠ 0 → κ ≤ Q'.coef e) →
        rowSupport Q' = Ustar → colSupport Q' = Vstar →
        ((crossCount M Ustar V : ℕ) : ℝ) ≤
          (2 * ((Rout + Q').eval (uniformPrices adj 3) - 3 * (Fintype.card L : ℝ)) +
            2 * offMass M Rout + offMass M Q) / κ := by sorry

end OncePaid.Sparse
