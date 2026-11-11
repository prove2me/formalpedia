-- Prove2me | Theorems.Thm_KeySchedules_Iterative_step_3_log_F
-- name    : KeySchedules.Iterative.step_3_log_F
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:24.607195+00:00
-- url     : https://prove2.me/theorems/78ab4ca4-8ebd-4fe5-a0c8-e5e0ac70c38b
-- title:
--   Proof of Lemma 3.2, Step 3 — F′(θ) ≤ μ e^{2r²θ/|S|} F(θ) and log F(θ) ≤ (μ|S|/(2r²))(e^{2r²θ/|S|} − 1)
-- statement:
--   Let $\mathrm{Out}$ be balanced, $h:G^r\to[0,1]$, $F(\theta)=\mathbb E\,e^{\theta X}$ and $\mu=\mathbb E X$ for a uniform permutation $\varphi$ of $S$. For every $\theta\ge0$:
--   $$F'(\theta)=\mathbb E[Xe^{\theta X}]=\frac1{|S|}\sum_{s,z}\tilde h(z)\Pr[E_{s,z}]\,\mathbb E[e^{\theta X}\mid E_{s,z}]\le\mu\,e^{2r^2\theta/|S|}F(\theta),$$
--   the sum ranging over the pairs with $\Pr[E_{s,z}]>0$, and
--   $$\log F(\theta)\le\frac{\mu|S|}{2r^2}\bigl(e^{2r^2\theta/|S|}-1\bigr).$$
--   With $\theta=|S|/(2r^2)$ and (12) this gives the exponential-moment bound behind Lemma 3.2.
--
--   Differences from the source:
--
--   - encoding: F′(θ) = E[X e^{θX}] → HasDerivAt F (E[X e^{θX}]) θ; reason: F is a finite sum of exponentials; HasDerivAt states both that the derivative exists and its value
--   - encoding: ∑_{s,z} over pairs with Pr[E_{s,z}] > 0 → ∑_s of a finsum over the finite set of z with some φ having Path_φ(s) = z; reason: same index set
--   - encoding: Pr_φ / E_φ for a uniform permutation φ of S → counts and averages over the finite type Equiv.Perm S; reason: uniform probability on a finite set is a counting ratio; same statement
--   - encoding: |G| ∣ |S| and |Out⁻¹(k)| = |S|/|G| for every k → IsBalanced Out: |Out⁻¹(k)| · |G| = |S| for every k; reason: equivalent; the product form implies the divisibility, so it is not a separate hypothesis
--   - encoding: h : G^r → [0, 1] → h : (Fin r → G) → ℝ with 0 ≤ h ≤ 1 as hypotheses; reason: same functions
--   - encoding: rounds and coordinates 1, …, r → Fin r, index i standing for round i + 1; reason: index base only
--   - reading: F′(θ) = E[X e^{θX}] and its expansion over (s, z), displayed after 'for θ ≥ 0' → these two clauses stated for θ ≥ 0, under the item's hypothesis hθ; reason: the page derives them in the paragraph fixed to θ ≥ 0, and only uses them there (integrating from 0 to θ)
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 13, proof of Lemma 3.2, Step 3

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Schedule

namespace KeySchedules.Iterative

/-- Proof of Lemma 3.2, Step 3 (p. 13): for `θ ≥ 0`,
* `F′(θ) = E[X e^{θX}]`;
* `E[X e^{θX}] = (1/|S|) ∑_{s,z} h̃(z) Pr[E_{s,z}] E[e^{θX} | E_{s,z}]`, the sum over the pairs
  with `Pr[E_{s,z}] > 0`;
* `E[X e^{θX}] ≤ μ e^{2r²θ/|S|} F(θ)`;
* `log F(θ) ≤ (μ|S|/(2r²)) (e^{2r²θ/|S|} − 1)`. -/
theorem step_3_log_F {S G : Type} [AddCommGroup G] [Fintype G] [Fintype S]
    [DecidableEq S] [Nonempty S] (r : ℕ) (hr : 1 ≤ r) (Out : S → G) (hOut : IsBalanced Out)
    (h : (Fin r → G) → ℝ) (h0 : ∀ k, 0 ≤ h k) (h1 : ∀ k, h k ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    HasDerivAt (mgfF Out h)
      ((Fintype.card (Equiv.Perm S) : ℝ)⁻¹ *
        ∑ φ : Equiv.Perm S, avgX Out h φ * Real.exp (θ * avgX Out h φ)) θ ∧
    (Fintype.card (Equiv.Perm S) : ℝ)⁻¹ *
        ∑ φ : Equiv.Perm S, avgX Out h φ * Real.exp (θ * avgX Out h φ)
      = (Fintype.card S : ℝ)⁻¹ * ∑ s : S,
          ∑ᶠ z ∈ {z : Fin r → S | ∃ φ : Equiv.Perm S, statePath φ r s = z},
            htilde Out h z *
              (({φ : Equiv.Perm S | statePath φ r s = z}.ncard : ℝ) /
                (Fintype.card (Equiv.Perm S) : ℝ)) * condMgf Out h s z θ ∧
    (Fintype.card (Equiv.Perm S) : ℝ)⁻¹ *
        ∑ φ : Equiv.Perm S, avgX Out h φ * Real.exp (θ * avgX Out h φ)
      ≤ meanMu Out h * Real.exp (2 * (r : ℝ) ^ 2 * θ / (Fintype.card S : ℝ)) * mgfF Out h θ ∧
    Real.log (mgfF Out h θ)
      ≤ meanMu Out h * (Fintype.card S : ℝ) / (2 * (r : ℝ) ^ 2) *
          (Real.exp (2 * (r : ℝ) ^ 2 * θ / (Fintype.card S : ℝ)) - 1) := by sorry

end KeySchedules.Iterative
