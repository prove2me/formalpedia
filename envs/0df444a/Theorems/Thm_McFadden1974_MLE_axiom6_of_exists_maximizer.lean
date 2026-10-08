-- Prove2me | Theorems.Thm_McFadden1974_MLE_axiom6_of_exists_maximizer
-- name    : McFadden1974.MLE.axiom6_of_exists_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:11.627841+00:00
-- url     : https://prove2.me/theorems/68805a86-43d2-4f9d-81a3-24662bcc80a6
-- title:
--   Lemma 3, proof — Axiom 6 is necessary for a maximizer of the log-likelihood
-- statement:
--   In the conditional logit model with every trial observed ($R_n \ge 1$) and the full-rank Axiom 5, suppose the log-likelihood $L$ of Equation (18) has a global maximizer $\hat\theta \in \mathbb{R}^K$. Then Axiom 6 holds: there is no nonzero $\gamma \in \mathbb{R}^K$ with
--   $$S_{in}(z_{jn} - z_{in})\gamma \le 0 \quad \text{for all } i, j = 1,\dots,J_n,\ n = 1,\dots,N.$$
--
--   This is the necessity half of Lemma 3: if some direction makes every observed choice weakly best, the likelihood keeps increasing along it and no maximizer exists.
--
--   **Formalization Note** Without $R_n \ge 1$ for every trial the statement fails: a trial with $R_n = 0$ can supply the rank of Axiom 5 while contributing nothing to $L$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), Lemma 3, proof (necessity)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Lemma 3, proof — necessity of Axiom 6** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116, PDF p. 12): "We first
show Axiom 6 to be necessary. Suppose L has a maximum at θ̂, but Axiom 6 fails for some γ ≠ 0. …
Hence, Axiom 6 is necessary."

Under Axiom 5, if the log-likelihood `L` attains a global maximum on `ℝ^K`, then Axiom 6 holds.

**Formalization Note.** Axioms 1–4 are built into the model `Data` (the logit form (16) and the
likelihood (18)); `Data.observed` is the standing assumption `R_n ≥ 1`, without which the claim
fails. -/
theorem axiom6_of_exists_maximizer
    {K : ℕ} (d : Data K) (h5 : d.Axiom5)
    (hmax : ∃ θhat : EuclideanSpace ℝ (Fin K), ∀ θ, d.L θ ≤ d.L θhat) :
    d.Axiom6 := by sorry

end McFadden1974.MLE
