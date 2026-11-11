-- Prove2me | Theorems.Thm_KeySchedules_Iterative_eq_11
-- name    : KeySchedules.Iterative.eq_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:50:56.271169+00:00
-- url     : https://prove2.me/theorems/1a7b72eb-5065-45ca-86e0-f920e0d0fc35
-- title:
--   Proof of Lemma 3.2, Step 1, Eq. (11) — a good path has probability 1/(|S|)_r ≥ |S|^{−r}
-- statement:
--   For $r\le|S|$ and every good tuple $z\in S^r$ (inputs $s,z_1,\dots,z_{r-1}$ pairwise distinct, outputs $z_1,\dots,z_r$ pairwise distinct), a uniform permutation $\varphi$ of $S$ satisfies
--   $$\Pr_\varphi[\mathrm{Path}_\varphi(s)=z]=\frac1{(|S|)_r}\ \ge\ |S|^{-r}=\Pr[U=z],$$
--   where $(n)_r=n(n-1)\cdots(n-r+1)$ and $U$ is uniform on $S^r$. It compares random state paths with independent uniform tuples on good tuples.
--
--   Differences from the source:
--
--   - generalization: stated inside the proof of Lemma 3.2, whose setting also has G, a balanced Out and h → only S, r ≥ 1, s and z; reason: the displayed claim involves only φ, U, s, z and r; the Lean statement is the same claim with the unused setting dropped
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: (|S|)_r → Nat.descFactorial (card S) r; reason: the falling factorial of §2
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 11, proof of Lemma 3.2, Step 1, Eq. (11)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 1, Eq. (11) (p. 11): for `r ≤ |S|` and every good tuple `z`,
`Pr_φ[Path_φ(s) = z] = 1/(|S|)_r ≥ |S|^{−r} = Pr[U = z]`, for `φ` uniform on the permutations
of `S` and `U` uniform on `S^r`. -/
theorem eq_11 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (r : ℕ) (hr : 1 ≤ r)
    (s : S) (z : Fin r → S) (hrS : r ≤ Fintype.card S) (hz : IsGood s z) :
    ({φ : Equiv.Perm S | statePath φ r s = z}.ncard : ℝ) / (Fintype.card (Equiv.Perm S) : ℝ)
        = 1 / ((Fintype.card S).descFactorial r : ℝ) ∧
    ((Fintype.card S : ℝ) ^ r)⁻¹ ≤ 1 / ((Fintype.card S).descFactorial r : ℝ) ∧
    ({U : Fin r → S | U = z}.ncard : ℝ) / (Fintype.card S : ℝ) ^ r
        = ((Fintype.card S : ℝ) ^ r)⁻¹ := by sorry

end KeySchedules.Iterative
