-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_3
-- name    : LogitRankDistill.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:50.035602+00:00
-- url     : https://prove2.me/theorems/6e584d6b-fa17-42e6-a847-c00c26bc853a
-- title:
--   Lemma 5.3 — the total variation between two softmax distributions is at most a quarter of the sup-distance of their logits
-- statement:
--   For vectors $L,L'\in\mathbb R^\Sigma$ let $P=\mathrm{softmax}(L)$ and $P'=\mathrm{softmax}(L')$. Then
--   $$D_{TV}(P,P')\le\frac14\,\|L-L'\|_\infty .$$
--   This is the Lipschitz estimate the paper uses to pass from logit errors to total variation in the proof of Theorem 5.11 (which needs only $D_{TV}\le\min\{1,\|L-L'\|_\infty\}$). As printed the constant $\tfrac14$ is false (two tokens, $L=0$, $L'=(0.1,-0.1)$ give $D_{TV}\approx0.0498>0.025$); it is stated as printed and the finding is recorded separately.
--
--   **Formalization Note.** $\|L-L'\|_\infty=\sup_y|L(y)-L'(y)|$ is `⨆ y, |L y - L' y|` over the finite type; $D_{TV}$ is $\tfrac12\sum_y|P(y)-P'(y)|$.
--
--   Differences from the source: none.
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 23, Lemma 5.3

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_LogitRankDistill_Models

namespace LogitRankDistill

/-- **Lemma 5.3** (p. 23): for `L, L' ∈ ℝ^Σ`,
`D_TV(softmax L, softmax L') ≤ (1/4) ‖L − L'‖_∞`. (False as printed: see the mission's
INSIGHTS, finding I1.) -/
theorem lemma_5_3 {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (L L' : Tok → ℝ) :
    IsingLTL.BeliefProp.tvDist (softmax L) (softmax L') ≤ (1 / 4) * ⨆ y, |L y - L' y| := by sorry

end LogitRankDistill
