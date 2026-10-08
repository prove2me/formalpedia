-- Prove2me | Theorems.Thm_MulticlassDS_Compress_fact14_leave_one_out
-- name    : MulticlassDS.Compress.fact14_leave_one_out
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:21:28.29162+00:00
-- url     : https://prove2.me/theorems/dd2b0edc-226f-4d44-9255-ac8190e7fd2b
-- title:
--   Fact 14, p. 11 — leave-one-out symmetrization
-- statement:
--   Let $\mathcal D$ be a distribution over a set $\mathcal Z$ and let $n>0$. For every event $E\subseteq\mathcal Z^{n+1}$,
--   $$\Pr_{(S,Z)\sim\mathcal D^{n+1}}\big[(S,Z)\in E\big] = \Pr_{(S',I)\sim\mathcal D^{n+1}\times U(n+1)}\big[(S'_{-I},S'_I)\in E\big],$$
--   where $U(n+1)$ is the uniform distribution on $[n+1]$, $S'_{-I}$ is $S'$ with its $I$-th entry deleted and $S'_I$ is that entry.
--
--   This exchangeability identity converts the expected error of a learner on a fresh test point into an average over leave-one-out runs on a single sample; it is used in Propositions 32 and 34.
--
--   **Formalization Note** $\mathcal D$ is a discrete distribution (`PMF`). The probability over $I\sim U(n+1)$ is written as the average $\frac1{n+1}\sum_{I}$. The pair $(S'_{-I},S'_I)$ is the word `Fin.snoc (s ∘ I.succAbove) (s I)`, so its first $n$ coordinates are $S'_{-I}$ and its last is $S'_I$.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 11, Fact 14

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Probability
open scoped ENNReal

namespace MulticlassDS.Compress

theorem fact14_leave_one_out {Z : Type*} (D : PMF Z) (n : ℕ) (hn : 0 < n)
    (E : Set (Fin (n + 1) → Z)) :
    iidProb D (n + 1) E = (1 / ((n : ℝ≥0∞) + 1)) * ∑ I : Fin (n + 1),
      iidProb D (n + 1) {s | Fin.snoc (s ∘ I.succAbove) (s I) ∈ E} := by sorry

end MulticlassDS.Compress
