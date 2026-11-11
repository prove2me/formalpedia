-- Prove2me | Theorems.Thm_KeySchedules_Iterative_step_3_cond_moment
-- name    : KeySchedules.Iterative.step_3_cond_moment
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:25.987235+00:00
-- url     : https://prove2.me/theorems/ae502987-242d-4c30-98fa-af9dc2e99ba8
-- title:
--   Proof of Lemma 3.2, Step 3 — E[e^{θX} | E_{s,z}] ≤ e^{2r²θ/|S|} F(θ)
-- statement:
--   Let $\mathrm{Out}$ be balanced and $h:G^r\to[0,1]$, and write $F(\theta)=\mathbb E\,e^{\theta X}$ for a uniform permutation $\varphi$ of $S$. For every pair $(s,z)$ with $\Pr[E_{s,z}]>0$ and every $\theta\ge0$,
--   $$\mathbb E\bigl[e^{\theta X}\mid E_{s,z}\bigr]\le e^{2r^2\theta/|S|}\,F(\theta).$$
--   It is the conditional moment comparison that drives the differential inequality for $F$.
--
--   Differences from the source:
--
--   - encoding: E[e^{θX} | E_{s,z}] → condMgf: the sum of e^{θX(φ)} over φ ∈ E_{s,z} divided by |E_{s,z}|; reason: conditional expectation under a uniform distribution on a finite set
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: h : G^r → [0, 1] → h : (Fin r → G) → ℝ with 0 ≤ h ≤ 1 as hypotheses; reason: same functions
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 13, proof of Lemma 3.2, Step 3

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 3 (p. 13): for every pair `(s, z)` with `Pr[E_{s,z}] > 0` and every
`θ ≥ 0`, `E[e^{θX} | E_{s,z}] ≤ e^{2r²θ/|S|} F(θ)`, where `F(θ) = E e^{θX}` and `φ` is uniform. -/
theorem step_3_cond_moment {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S]
    [DecidableEq S] [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (h : (Fin r → G) → ℝ) (h0 : ∀ k, 0 ≤ h k) (h1 : ∀ k, h k ≤ 1)
    (s : S) (z : Fin r → S) (hpos : ∃ φ : Equiv.Perm S, statePath φ r s = z)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    condMgf Out h s z θ
      ≤ Real.exp (2 * (r : ℝ) ^ 2 * θ / (Fintype.card S : ℝ)) * mgfF Out h θ := by sorry

end KeySchedules.Iterative
