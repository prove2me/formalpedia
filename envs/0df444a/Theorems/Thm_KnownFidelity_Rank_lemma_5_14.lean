-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_5_14
-- name    : KnownFidelity.Rank.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:50.057885+00:00
-- url     : https://prove2.me/theorems/ffffd4d9-38b4-4bbb-a16f-05a70b69f896
-- title:
--   Lemma 5.14 — moments $1\le\mathbb ER_G^\ell\le\prod_{j<\ell}(1+j\zeta)\le\exp(\zeta\ell^2/2)$
-- statement:
--   Let $a\in\mathbb R^r_{\ge0}$ with $\sum_ia_i=1$, let $G\sim Q(a)$ be the doubly correlated Wishart factor of Eq. (40), so that $R_G=\|G\|_F^2=\sum_{i,j}a_ia_jX_{ij}$ with independent mean-one exponentials $X_{ij}$, and let $\zeta=\max_{i,j}a_ia_j$. Then for every integer $\ell\ge1$
--
--   $$1\ \le\ \mathbb E R_G^\ell\ \le\ \prod_{j=0}^{\ell-1}(1+j\zeta)\ \le\ \exp\Big(\frac{\zeta\ell^2}{2}\Big).$$
--
--   It controls the size-biased tilt in the separation argument of §5.6.
--
--   Differences from the source:
--   - generalization: a = a^{(1)} (the spread-out vector of Proposition 5.2) → any nonnegative a with Σ_i a_i = 1; reason: the lemma's proof uses only these properties; the paper's a^{(1)} satisfies them
--   - encoding: E R_G^ℓ → lower Lebesgue integral of ofReal(‖G‖_F^{2ℓ}) under wishartLaw a, compared in ℝ≥0∞; reason: the same moment, with no integrability junk
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.6, Eq. (76) and Lemma 5.14, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_wishartLaw
import Definitions.Def_KnownFidelity_Rank_frobSq

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Lemma 5.14 (moments of `R_G`).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.6, Eq. (76) and Lemma 5.14, printed p. 24 (PDF p. 26): "Write
R_G = ∥G∥²_F = Σ_{i,j} a^{(1)}_i a^{(1)}_j X_ij, (76) where the X_ij are independent mean-one
exponentials. The coefficients sum to one and satisfy ζ := max_{i,j} a^{(1)}_i a^{(1)}_j ≤ B²/r².
Lemma 5.14. For every integer ℓ ≥ 1, 1 ≤ E R_G^ℓ ≤ ∏_{j=0}^{ℓ−1} (1 + jζ) ≤ exp(ζℓ²/2). (77)"

For a nonnegative `a ∈ ℝ^r` with `Σ_i a_i = 1`, `G ∼ Q(a)` (Eq. (40)), `R_G = ‖G‖_F²` and
`ζ = max_{i,j} a_i a_j`, all three inequalities of (77) hold for every integer `ℓ ≥ 1`.

**Formalization Note.** `Q(a) = wishartLaw a`; the moment `E R_G^ℓ` is a lower integral in
`ℝ≥0∞` (no integrability junk). The lemma is stated for every such `a` (the paper applies it to
`a^{(1)}`); `ζ` is given as the greatest product `a_i a_j`. -/
theorem lemma_5_14 {r : ℕ} (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    (ζ : ℝ) (hζ : IsGreatest (Set.range fun p : Fin r × Fin r => a p.1 * a p.2) ζ)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    1 ≤ ∫⁻ G, ENNReal.ofReal (frobSq G ^ ℓ) ∂(wishartLaw a) ∧
    ∫⁻ G, ENNReal.ofReal (frobSq G ^ ℓ) ∂(wishartLaw a) ≤
      ENNReal.ofReal (∏ j ∈ Finset.range ℓ, (1 + j * ζ)) ∧
    ∏ j ∈ Finset.range ℓ, (1 + j * ζ) ≤ Real.exp (ζ * ℓ ^ 2 / 2) := by sorry

end KnownFidelity.Rank
