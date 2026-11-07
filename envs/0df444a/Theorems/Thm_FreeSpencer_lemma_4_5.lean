-- Prove2me | Theorems.Thm_FreeSpencer_lemma_4_5
-- name    : FreeSpencer.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:36.881481+00:00
-- url     : https://prove2.me/theorems/c73aade4-a123-45db-9e5b-46b7eb0b17d1
-- title:
--   Lemma 4.5, p.28 — elementary potential bounds
-- statement:
--   Let $\hat A_1,\dots,\hat A_\ell$ be real symmetric contractions and let $E,f$ be the potential and soft maximum for $0<q\le1/2$, $\theta>0$, $\kappa\ge0$. For every symmetric $H$ and covariance $0\preceq C\preceq I_\ell$,
--   $$0\le E(H,C)-f(H)\le2\sqrt\ell.$$
--   Both $E(\cdot,C)$ and $f$ are convex and $1$-Lipschitz for the operator norm, and $E(H,\cdot)$ is order preserving. Discarding any current covariance and installing the identity on $\ell$ live coordinates increases the potential by at most $2\sqrt\ell$. In square mode ($q=1/2$, $\theta=128$, $\kappa=0$) with $m\le n$, the lifted family satisfies
--   $$E(H(x),C)\ge\|H(x)\|_{op},\qquad E(0,I_n)\le(2+256\sqrt2)\sqrt n.$$
--   These facts make the potential a pseudo-value: it starts at $O(\sqrt n)$, dominates the loss at a signing, and a new epoch costs little.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - generalization: Lemma 4.5 for the square potential at θ → 0 < q ≤ 1/2, θ > 0, κ ≥ 0 for the bounds; reason: pp.57 and 63 repeat the bounds for these parameters; (4.10) stays at (1/2, 128, 0)
--   - generalization: the lifted center at a point x of the cube → every real x, every covariance on all n coordinates; reason: E ≥ λmax needs nothing about x; this specializes to the source
--   - encoding: a maximum over densities → sSup over densities; reason: attainment is proved in lemma_5_1 (Lemma 4.4); the set is nonempty and bounded
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 4.5, p.28; for general (q, θ, κ): Lemma 8.1, p.57, and (10.2), p.63

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_lift
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 4.5** (Elementary potential bounds), with (2.5) and (10.2).
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 4.5, p.28; for general `(q, θ, κ)`: Lemma 8.1, p.57, and (10.2), p.63.

**Formalization Note** The page states the bounds for the square potential, and pp.57, 63 repeat them
for `0 < q ≤ 1/2`, `κ ≥ 0`, as "the facts (7.3)" for either potential; all are stated here at once.
Maxima are `sSup`. `0 ⪯ C` with `C ⪯ I_ℓ` is `IsCov C`, and order preservation needs no upper bound.
(4.10) keeps all `n` coordinates (Remark 7.2, p.49) and holds at every real `x`. -/
theorem lemma_4_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (q θ κ : ℝ)
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    (∀ (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ), H.IsSymm → IsCov C →
      0 ≤ pot q θ κ Ah H C - softMax q θ κ H ∧ pot q θ κ Ah H C - softMax q θ κ H ≤ 2 * Real.sqrt ℓ) ∧
    (∀ C : Matrix (Fin ℓ) (Fin ℓ) ℝ, IsCov C →
      ConvexOn ℝ {H : Matrix ι ι ℝ | H.IsSymm} (fun H => pot q θ κ Ah H C) ∧
      ∀ H H' : Matrix ι ι ℝ, H.IsSymm → H'.IsSymm →
        |pot q θ κ Ah H C - pot q θ κ Ah H' C| ≤ ‖H - H'‖) ∧
    (ConvexOn ℝ {H : Matrix ι ι ℝ | H.IsSymm} (softMax q θ κ) ∧
      ∀ H H' : Matrix ι ι ℝ, H.IsSymm → H'.IsSymm →
        |softMax q θ κ H - softMax q θ κ H'| ≤ ‖H - H'‖) ∧
    (∀ (H : Matrix ι ι ℝ) (C C' : Matrix (Fin ℓ) (Fin ℓ) ℝ), H.IsSymm → C'.PosSemidef →
      (C - C').PosSemidef → pot q θ κ Ah H C' ≤ pot q θ κ Ah H C) ∧
    (∀ (ℓ₀ : ℕ) (Ah₀ : Fin ℓ₀ → Matrix ι ι ℝ) (C₀ : Matrix (Fin ℓ₀) (Fin ℓ₀) ℝ) (H : Matrix ι ι ℝ),
      IsContrFam Ah₀ → IsCov C₀ → H.IsSymm →
      pot q θ κ Ah H 1 - pot q θ κ Ah₀ H C₀ ≤ 2 * Real.sqrt ℓ) ∧
    (∀ (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ), m ≤ n →
      (∀ i, (A i).IsSymm) → (∀ i, ‖A i‖ ≤ 1) →
      (∀ (x : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ), IsCov C →
        ‖center A x‖ ≤ pot (1 / 2) 128 0 (liftFam A) (center A x) C) ∧
      pot (1 / 2) 128 0 (liftFam A) 0 1 ≤ (2 + 256 * Real.sqrt 2) * Real.sqrt n) := by sorry

end FreeSpencer
