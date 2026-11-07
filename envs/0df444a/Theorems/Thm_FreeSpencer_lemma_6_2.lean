-- Prove2me | Theorems.Thm_FreeSpencer_lemma_6_2
-- name    : FreeSpencer.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:21.441236+00:00
-- url     : https://prove2.me/theorems/5167e82c-8f08-4cff-b3d1-ca23503b3f8b
-- title:
--   Lemma 6.2, p.44 — response bound for the low parts
-- statement:
--   Let $P,R\succ0$ and $D_1,\dots,D_r$ be real symmetric with $\Phi(P)=P$. For real symmetric $D$, the half-response obtained from the square-root regularizer curvature alone is
--   $$\langle F(D),\tilde H_\theta^{-1}F(D)\rangle=q_\theta(D)=\theta^{-1}\|P^{1/2}DR^{1/2}\|_{HS}^2,$$
--   and it bounds the unconstrained half-response $\langle F(D),\tilde H^{-1}F(D)\rangle$ from above. If $\mathrm{Tr}\,P\le\sqrt\ell$, $\mathrm{Tr}\,R^2\le\ell$ and $\epsilon=c/\sqrt\ell$ with $c>0$, then
--   $$\sum_aq_\theta(D_a^l)\le\frac{4\sqrt{c\ell}}\theta.$$
--
--   Differences from the source:
--   - reading: "the half-response obtained from the square-root regularizer curvature alone … bounds the corresponding unconstrained half-response" → the identity ⟨F(D), H̃_θ⁻¹F(D)⟩ = q_θ(D) and the inequality ⟨F(D), H̃⁻¹F(D)⟩ ≤ q_θ(D); reason: the page derives the identity at the start of its proof, and these are the only readings of the two sentences
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.2, p.44; setting p.41; (6.5), p.42; (6.9), p.44

import Mathlib
import Definitions.Def_FreeSpencer_specProj
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 6.2** (Response bound for the low parts), in the abstract setting of Section 6: `P, R ≻ 0`,
real symmetric `Dₐ`, `Φ(P) = P`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.2, p.44; setting p.41; (6.5) p.42; (6.9) p.44.

**Formalization Note** The sentence "half-response obtained from the square-root regularizer
curvature alone" is the identity `⟨F(D), H̃_θ⁻¹ F(D)⟩ = q_θ(D)` from the page's proof; "It bounds the
corresponding unconstrained half-response" is `⟨F(D), H̃⁻¹ F(D)⟩ ≤ q_θ(D)`. -/
theorem lemma_6_2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ} (P R : Matrix ι ι ℝ) (D : Fin r → Matrix ι ι ℝ) (θ : ℝ)
    (hP : P.PosDef) (hR : R.PosDef) (hD : ∀ a, (D a).IsSymm) (hθ : 0 < θ) (hfix : opPhi D P = P) :
    (∀ D₀ : Matrix ι ι ℝ, D₀.IsSymm →
      hs (normKraus P D₀) (opHthetaInvTilde θ P R (normKraus P D₀)) = qTheta θ P R D₀ ∧
      hs (normKraus P D₀) (Ring.inverse (opHtilde θ P R D) (normKraus P D₀)) ≤ qTheta θ P R D₀) ∧
    (∀ (ℓ : ℕ) (c : ℝ), 1 ≤ ℓ → 0 < c → Matrix.trace P ≤ Real.sqrt ℓ → Matrix.trace (R * R) ≤ ℓ →
      ∑ a, qTheta θ P R (lowPart (c / Real.sqrt ℓ) P (D a)) ≤ 4 * Real.sqrt (c * ℓ) / θ) := by sorry

end FreeSpencer
