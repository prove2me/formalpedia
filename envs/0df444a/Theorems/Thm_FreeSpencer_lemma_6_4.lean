-- Prove2me | Theorems.Thm_FreeSpencer_lemma_6_4
-- name    : FreeSpencer.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:04.694211+00:00
-- url     : https://prove2.me/theorems/934480b3-f896-464e-862b-e71181a728ff
-- title:
--   Lemma 6.4, p.47 — the comparison term of the high parts
-- statement:
--   In the setting of Section 6, with $\epsilon>0$,
--   $$\mathrm{Tr}_{HS}(\Sigma_hK_0)=\theta^{-1}\mathrm{Tr}(RW_h).$$
--   If also $\mathrm{Tr}\,P\le\sqrt\ell$, $\mathrm{Tr}\,R^2\le\ell$, $G\preceq tI$ with $t=L/\sqrt\ell$, and $\epsilon=c/\sqrt\ell$, then
--   $$\mathrm{Tr}_{HS}(\Sigma_hK_0)\le\frac{2L^2}{c^{3/2}\theta}\sqrt\ell.$$
--   Here $\Sigma_h$ is the frame operator of the normalized high parts. Together with Lemma 6.2 this gives the constants of Theorem 6.5.
--
--   Differences from the source:
--   - reading: "If (6.5) holds, t = L/√ℓ, and ε = c/√ℓ" → adds L, c > 0, ℓ ≥ 1 and G ⪯ t I, the assumption of Lemma 6.1 that Lemma 6.3 and this proof use; reason: the page defines t only through that assumption (p.42, p.45)
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.4, p.47; Lemma 6.1, p.42; Lemma 6.3, p.45; (6.5), p.42; (6.9), p.44

import Mathlib
import Definitions.Def_FreeSpencer_specProj
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 6.4** (Exact identity for the comparison term of the high parts), (6.18) and (6.19), in the
setting of Section 6. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.4, p.47; Lemma 6.1, p.42; Lemma 6.3, p.45;
(6.5) p.42; (6.9) p.44.

**Formalization Note** `Σ_h = ∑ₐ |F_aʰ⟩⟨F_aʰ|` is `opSigma P Dʰ`. (6.19) adds, as the page does, (6.5)
and the hypothesis `G ⪯ t I` of Lemma 6.1, with `t = L/√ℓ`, `ε = c/√ℓ`. -/
theorem lemma_6_4 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ} (P R : Matrix ι ι ℝ) (D : Fin r → Matrix ι ι ℝ) (θ : ℝ)
    (hP : P.PosDef) (hR : R.PosDef) (hD : ∀ a, (D a).IsSymm) (hθ : 0 < θ) (hfix : opPhi D P = P) :
    (∀ ε : ℝ, 0 < ε →
      trHS (opSigma P (fun a => highPart ε P (D a)) * opK0 θ P R D) =
        θ⁻¹ * Matrix.trace (R * highW ε P D)) ∧
    (∀ (ℓ : ℕ) (L c : ℝ), 1 ≤ ℓ → 0 < L → 0 < c →
      Matrix.trace P ≤ Real.sqrt ℓ → Matrix.trace (R * R) ≤ ℓ →
      ((L / Real.sqrt ℓ) • (1 : Matrix (Fin r) (Fin r) ℝ) - gramG P D).PosSemidef →
      trHS (opSigma P (fun a => highPart (c / Real.sqrt ℓ) P (D a)) * opK0 θ P R D) ≤
        2 * L ^ 2 / (c ^ (3 / 2 : ℝ) * θ) * Real.sqrt ℓ) := by sorry

end FreeSpencer
