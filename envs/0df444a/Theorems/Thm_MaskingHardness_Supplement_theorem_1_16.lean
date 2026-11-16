-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_16
-- name    : MaskingHardness.Supplement.theorem_1_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:35:07.768192+00:00
-- url     : https://prove2.me/theorems/e2c60069-aade-4970-8809-25ba8a5415ae
-- title:
--   Theorem 1.16 — entropy surrogates (corrected: $\mathcal B$ nonempty)
-- statement:
--   Let $\mathcal A,\mathcal B,\mathcal Y$ be sets with $\mathcal Y$ and $\mathcal B$ finite and $\mathcal B$ nonempty, let $\beta\ge0$, and let $\ell_{\mathcal A}:\mathcal Y\times\mathcal A\to\mathbb R$ and $\ell_{\mathcal B}:\mathcal Y\times\mathcal B\to\mathbb R$ be finite losses with entropy functions $h_{\mathcal A},h_{\mathcal B}:\Delta(\mathcal Y)\to\overline{\mathbb R}$ (Definition 1.15). Then $\ell_{\mathcal A}$ is a $\beta$-surrogate for $\ell_{\mathcal B}$ (Definition 1.14) if and only if
--
--   $$
--   h_{\mathcal A}(p)\ \ge\ \beta\,h_{\mathcal B}(p)\qquad\text{for all }p\in\Delta(\mathcal Y).
--   $$
--
--   Whether a loss is a surrogate for another (for instance for the 0-1 loss) is thus decided by comparing entropy functions alone, which is how the surrogate coefficients of the weak, strong and Crammer–Singer hinge losses are computed.
--
--   **Formalization Note** $\mathcal A$ is an arbitrary type (possibly empty or infinite); entropies are `EReal` infima and $\beta h_{\mathcal B}(p)$ is the `EReal` product.
--
--   Differences from the source:
--   - correction: ℓA is a β-surrogate for ℓB iff hA ≥ β hB, for B finite (possibly empty) → the same equivalence with B finite and nonempty ([Nonempty B]); reason: for B = ∅, β = 0, A nonempty and ℓA ≥ 0 (Y nonempty) the entropy side holds (hB = +∞ and 0·(+∞) = 0 ≤ hA) while no rounding A → Δ(∅) exists, since Δ(∅) is empty; with Y = ∅ the right side is vacuous and the left side again fails
--   - encoding: entropies hA, hB : Δ(Y) → ℝ̄ and the product β hB(p) → EReal infima (lossEntropy) and the EReal product (β : EReal) * hB p; reason: ℝ̄ is EReal; for real β ≥ 0 and finite hB(p) the product is the real product
--   - encoding: Δ(Y), Δ(B) and a rounding R : A → Δ(B) → stdSimplex ℝ Y, stdSimplex ℝ B and R : A → B → ℝ with R a ∈ stdSimplex ℝ B; reason: the standard simplex is the set of probability vectors
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.16, p.9 (PDF p.11); restated with proof pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_MaskingHardness_Supplement_IsSurrogate
import Definitions.Def_MaskingHardness_Supplement_lossEntropy

namespace MaskingHardness.Supplement

/-- **Theorem 1.16** (Entropy Surrogates) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.16, printed p.9 = PDF p.11; restated
with proof printed pp.26–27 = PDF pp.28–29) (corrected: `B` nonempty).

Given sets `A, B, Y`, `β ≥ 0` and finite losses `ℓA : Y × A → ℝ`, `ℓB : Y × B → ℝ` with entropy
functions `hA, hB : Δ(Y) → ℝ̄`: if `Y` and `B` are finite, then `ℓA` is a `β`-surrogate for `ℓB`
if and only if `hA(p) ≥ β hB(p)` for all `p ∈ Δ(Y)`.

**Formalization Note** Correction: `B` is assumed nonempty. Without it the equivalence fails: for
`B = ∅`, `β = 0`, `A` nonempty and `ℓA ≥ 0`, the entropy side holds (`hB = +∞`, `0 · (+∞) = 0 ≤ hA`)
while no rounding `A → Δ(∅)` exists. `A` is an arbitrary type (possibly empty or infinite); `hA, hB`
are `EReal` infima (`lossEntropy`); `β hB(p)` is the `EReal` product. -/
theorem theorem_1_16 {Y A B : Type*} [Fintype Y] [Fintype B] [Nonempty B]
    (β : ℝ) (hβ : 0 ≤ β) (ℓA : Y → A → ℝ) (ℓB : Y → B → ℝ) :
    IsSurrogate β ℓA ℓB ↔
      ∀ p ∈ stdSimplex ℝ Y, (β : EReal) * lossEntropy ℓB p ≤ lossEntropy ℓA p := by sorry

end MaskingHardness.Supplement
