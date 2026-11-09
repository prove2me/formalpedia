-- Prove2me | Theorems.Thm_LinfContractionFP_eq_9
-- name    : LinfContractionFP.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:29.713692+00:00
-- url     : https://prove2.me/theorems/6baa4637-0ae3-456e-96f2-b1ad483acbdb
-- title:
--   Eq. (9) — the recursive potential is dominated
-- statement:
--   Let $\sigma,b,\delta$ be vectors with $|\delta_i|\le2\tau$ for all $i$, and let $\tau''=\tau/32$ or $\tau''=\tau/2$. Then the potential $\Phi_+$ of the shift $b+\delta$ at tolerance $\tau''$ is at most the potential $\Phi_+$ of the shift $b$ at tolerance $\tau$:
--   $$\Phi^{\delta,\tau''}_+(F)\le\Phi_+(F).$$
--   Consequently every recursive call of Amplify made with the unscaled budget $B_+$ meets the precondition of Contract 1.
--
--   Differences from the source:
--   - reading: Φ^{δ,τ′}_+(F) ≤ Φ+(F) with τ′ in (9) → τ'' = τ/32 or τ/2, as in the surrounding text; reason: the prime count in (9) is a typographical variant of τ''
--   - reading: every δ_i is in [−2τ, 2τ] 'by direct inspection of Algorithm 3' → hypothesis |δ_i| ≤ 2τ; reason: the range is read off Algorithm 3; the inequality is stated for any such δ
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), proof of Lemma 4, display (9), p.17

import Mathlib
import Definitions.Def_LinfContractionFP_potentials

namespace LinfContractionFP

/-- Display (9), in the proof of Lemma 4: if every shift `δ_i` lies in `[−2τ, 2τ]`, the potential
`Φ₊` of the recursive call (shift `b + δ`, tolerance `τ'' = τ/32` or `τ/2`) is at most the
potential `Φ₊` of the current call (shift `b`, tolerance `τ`).

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), proof of Lemma 4, p.17: "we therefore have to relate the exponential weight potentials
Φ^{δ,τ''}_+(F) for b + δ at tolerance τ'' = τ/32 and τ'' = τ/2. We claim that
Φ^{δ,τ'}_+(F) ≤ Φ+(F). (9) [...] By direct inspection of Algorithm 3, it is clear that every δ_i
must be in the range [−2τ, 2τ]."

**Formalization Note.** The `τ'` printed in (9) is the `τ''` of the surrounding text. The range
of `δ` is a hypothesis (the paper reads it off Algorithm 3). -/
theorem eq_9 {κ : Type} [Fintype κ] (σ b δ : κ → ℝ) (τ τ'' : ℝ) (F : κ → ℤ)
    (hδ : ∀ i, |δ i| ≤ 2 * τ) (hτ'' : τ'' = τ / 32 ∨ τ'' = τ / 2) :
    phiPlus σ (b + δ) τ'' F ≤ phiPlus σ b τ F := by sorry

end LinfContractionFP
