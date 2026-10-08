-- Prove2me | Theorems.Thm_McFadden1974_MLE_exists_maximizer_iff_axiom6
-- name    : McFadden1974.MLE.exists_maximizer_iff_axiom6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:43.308776+00:00
-- url     : https://prove2.me/theorems/2ecbec82-18f8-4eef-a8e0-c48c87f3441d
-- title:
--   Lemma 3 — under Axioms 1–5 the log-likelihood has a maximizer iff Axiom 6 holds
-- statement:
--   Consider a conditional logit choice experiment: $N$ trials, trial $n$ with $J_n$ alternatives of attribute vectors $z_{in} \in \mathbb{R}^K$, repeated $R_n \ge 1$ times with alternative $i$ chosen $S_{in}$ times, and log-likelihood (18)
--   $$L(\theta) = C - \sum_{n=1}^N \sum_{i=1}^{J_n} S_{in} \log \sum_{j=1}^{J_n} e^{(z_{jn}-z_{in})\theta}.$$
--   Suppose the full-rank Axiom 5 holds. Then $L$ has a global maximizer on $\mathbb{R}^K$ if and only if Axiom 6 holds, that is, if and only if there is no nonzero $\gamma \in \mathbb{R}^K$ with
--   $$S_{in}(z_{jn} - z_{in})\gamma \le 0 \quad \text{for all } i, j = 1,\dots,J_n,\ n = 1,\dots,N.$$
--
--   Lemma 3 decides when the conditional logit maximum likelihood estimator exists in a finite sample: it fails exactly when some direction in parameter space makes every observed choice weakly best in its alternative set.
--
--   **Formalization Note** Axioms 1–4 are built into the model through the logit form (16) and the likelihood (18), so "Suppose Axioms 1–5 hold" becomes the model plus Axiom 5. Every trial is assumed observed ($R_n \ge 1$), as implicit in the paper; without it necessity fails. Axiom 5 is read at every $\theta$; its row space does not depend on $\theta$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), Lemma 3

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Lemma 3** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116, PDF p. 12): "Suppose Axioms 1–5 hold. Then Axiom 6 is
necessary and sufficient for the existence of a vector θ maximizing L."

For conditional logit data with every trial observed (`R_n ≥ 1`) and satisfying the full-rank
Axiom 5, the log-likelihood (18) has a global maximizer on `ℝ^K` if and only if Axiom 6 holds.

**Formalization Note.** Axioms 1–3 (which give the logit form (12)) and Axiom 4 (linearity of
`v` in `θ`) are built into the model `Data`: the selection probabilities are (16) and `L` is (18).
"Suppose Axioms 1–5 hold" therefore becomes: the model `Data` plus `Axiom5`. `Data.observed` is
the standing assumption `R_n ≥ 1` for every trial; without it necessity fails. Axiom 5 is read at
every `θ`; its row space does not depend on `θ`. -/
theorem exists_maximizer_iff_axiom6
    {K : ℕ} (d : Data K) (h5 : d.Axiom5) :
    (∃ θhat : EuclideanSpace ℝ (Fin K), ∀ θ, d.L θ ≤ d.L θhat) ↔ d.Axiom6 := by sorry

end McFadden1974.MLE
