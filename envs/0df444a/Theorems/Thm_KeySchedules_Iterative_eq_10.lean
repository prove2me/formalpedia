-- Prove2me | Theorems.Thm_KeySchedules_Iterative_eq_10
-- name    : KeySchedules.Iterative.eq_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:50:54.101066+00:00
-- url     : https://prove2.me/theorems/09bff8e3-fb19-4a1d-bca8-c07d872ed09f
-- title:
--   Proof of Lemma 3.2, Step 1, Eq. (10) — a uniform r-tuple is bad with probability at most r(r − 1)/|S|
-- statement:
--   Fix a master key $s\in S$ and let $U=(U_1,\dots,U_r)$ consist of independent uniform elements of $S$. Then $\Pr[U_i=U_j]=\Pr[U_i=s]=1/|S|$ for $i\neq j$, and the probability that $U$ is bad (the inputs $s,U_1,\dots,U_{r-1}$ or the outputs $U_1,\dots,U_r$ are not pairwise distinct) satisfies
--   $$\Pr[U\text{ is bad}]\le\frac{2\binom r2}{|S|}=\frac{r(r-1)}{|S|}.$$
--   This is the birthday-type estimate that controls the difference between a random state path and a uniform tuple in the mean bound (12).
--
--   Differences from the source:
--
--   - generalization: stated inside the proof of Lemma 3.2, whose setting also has G, a balanced Out and h → only S, r ≥ 1 and s; reason: the displayed claim involves only U, s and r; the Lean statement is the same claim with the unused setting dropped
--   - encoding: U uniform on S^r, Pr[·] → counts over Fin r → S divided by |S|^r; reason: uniform probability on a finite set as a counting ratio
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 11, proof of Lemma 3.2, Step 1, Eq. (10)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 1, Eq. (10) (p. 11): fix a master key `s` and let
`U = (U_1, …, U_r)` be uniform on `S^r` (probabilities are counts divided by `|S|^r`). Then
`Pr[U_i = U_j] = Pr[U_i = s] = 1/|S|` for `i ≠ j`, and the probability that `U` is bad (not
good: the inputs `s, U_1, …, U_{r−1}` or the outputs `U_1, …, U_r` are not pairwise distinct)
is at most `2·C(r,2)/|S| = r(r − 1)/|S|`. -/
theorem eq_10 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (r : ℕ) (hr : 1 ≤ r)
    (s : S) :
    (∀ i j : Fin r, i ≠ j →
      ({U : Fin r → S | U i = U j}.ncard : ℝ) / (Fintype.card S : ℝ) ^ r
        = 1 / (Fintype.card S : ℝ)) ∧
    (∀ i : Fin r,
      ({U : Fin r → S | U i = s}.ncard : ℝ) / (Fintype.card S : ℝ) ^ r
        = 1 / (Fintype.card S : ℝ)) ∧
    ({U : Fin r → S | ¬ IsGood s U}.ncard : ℝ) / (Fintype.card S : ℝ) ^ r
      ≤ 2 * (r.choose 2 : ℝ) / (Fintype.card S : ℝ) ∧
    2 * (r.choose 2 : ℝ) / (Fintype.card S : ℝ)
      = (r : ℝ) * ((r : ℝ) - 1) / (Fintype.card S : ℝ) := by sorry

end KeySchedules.Iterative
