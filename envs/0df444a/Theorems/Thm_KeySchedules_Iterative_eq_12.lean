-- Prove2me | Theorems.Thm_KeySchedules_Iterative_eq_12
-- name    : KeySchedules.Iterative.eq_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:05.226866+00:00
-- url     : https://prove2.me/theorems/a31fdb60-a559-4263-b6e5-2562dc28e80b
-- title:
--   Proof of Lemma 3.2, Step 1, Eq. (12) — the mean bound μ ≤ α + r(r − 1)/|S|
-- statement:
--   Let $\mathrm{Out}:S\to G$ be balanced and $h:G^r\to[0,1]$. For every master key $s$,
--   $$\mathbb E_\varphi\,h(\mathrm{KS}_\varphi(s))\le\alpha+\frac{r(r-1)}{|S|},$$
--   and averaging over $s\leftarrow S$,
--   $$\mu=\mathbb E_\varphi X(\varphi)\le\alpha+\frac{r(r-1)}{|S|},\qquad \alpha=\mathbb E_{k\leftarrow G^r}h(k).$$
--   No relation between $r$ and $|S|$ is assumed. The bound feeds the choice $\theta=|S|/(2r^2)$ in Step 3.
--
--   Differences from the source:
--
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: h : G^r → [0, 1] → h : (Fin r → G) → ℝ with 0 ≤ h ≤ 1 as hypotheses; reason: same functions
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 12, proof of Lemma 3.2, Step 1, Eq. (12)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 1, Eq. (12) (p. 12): for `h : G^r → [0, 1]` and balanced `Out`,
every master key `s` has `E_φ h(KS_φ(s)) ≤ α + r(r − 1)/|S|`, and averaging over `s`,
`μ = E_φ X(φ) ≤ α + r(r − 1)/|S|`, where `α = E_{k←G^r} h(k)`. No `r ≤ |S|` is assumed. -/
theorem eq_12 {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S] [DecidableEq S]
    [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (h : (Fin r → G) → ℝ) (h0 : ∀ k, 0 ≤ h k) (h1 : ∀ k, h k ≤ 1) :
    (∀ s : S,
      (Fintype.card (Equiv.Perm S) : ℝ)⁻¹ * ∑ φ : Equiv.Perm S, h (KS Out r φ s)
        ≤ alphaMean h + (r : ℝ) * ((r : ℝ) - 1) / (Fintype.card S : ℝ)) ∧
    meanMu Out h ≤ alphaMean h + (r : ℝ) * ((r : ℝ) - 1) / (Fintype.card S : ℝ) := by sorry

end KeySchedules.Iterative
