-- Prove2me | Theorems.Thm_KeySchedules_Iterative_lemma_3_2
-- name    : KeySchedules.Iterative.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:27.893204+00:00
-- url     : https://prove2.me/theorems/831615a3-1065-494b-b3d0-24d964239b15
-- title:
--   Lemma 3.2 — tail bound for the master-key average under the iterative key schedule
-- statement:
--   Let $G$ be a finite abelian group, $S$ a nonempty finite set, $r\ge1$, $\mathrm{Out}:S\to G$ balanced, and $\mathrm{KS}_\varphi$ the iterative key schedule (8) of a uniform permutation $\varphi$ of $S$. For every $h:G^r\to[0,1]$ and every $u\ge0$,
--   $$\Pr_\varphi\Bigl[\mathbb E_{s\leftarrow S}h(\mathrm{KS}_\varphi(s))>(e-1)\,\mathbb E_{k\leftarrow G^r}h(k)+\frac{2r^2}{|S|}(u+1)\Bigr]\le e^{-u}.$$
--   It is the concentration statement that Theorem 3.2 applies to $h=g^\star(\bar\tau,\cdot)$ for each transcript $\bar\tau\in\mathcal T_q$; it replaces Lemma 3.1, where the keys of distinct master keys are independent.
--
--   Differences from the source:
--
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: Pr_φ[…] ≤ e^{−u} → card {φ | …} ≤ e^{−u} · card (Equiv.Perm S); reason: uniform probability on a finite set as a counting ratio
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: h : G^r → [0, 1] → h : (Fin r → G) → ℝ with 0 ≤ h ≤ 1 as hypotheses; reason: same functions
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 11, Lemma 3.2, Eq. (9)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Lemma 3.2 (p. 11): for the key schedule (8) and `h : G^r → [0, 1]`, for every `u ≥ 0`,
`Pr_φ[E_{s←S} h(KS_φ(s)) > (e − 1) E_{k←G^r} h(k) + (2r²/|S|)(u + 1)] ≤ e^{−u}`, for `φ`
uniform on the permutations of `S`; stated as a count of permutations. -/
theorem lemma_3_2 {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S] [DecidableEq S]
    [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (h : (Fin r → G) → ℝ) (h0 : ∀ k, 0 ≤ h k) (h1 : ∀ k, h k ≤ 1) (u : ℝ) (hu : 0 ≤ u) :
    ({φ : Equiv.Perm S | avgX Out h φ >
        (Real.exp 1 - 1) * alphaMean h + 2 * (r : ℝ) ^ 2 / (Fintype.card S : ℝ) * (u + 1)}.ncard
        : ℝ)
      ≤ Real.exp (-u) * (Fintype.card (Equiv.Perm S) : ℝ) := by sorry

end KeySchedules.Iterative
