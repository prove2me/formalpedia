-- Prove2me | Theorems.Thm_FreeSpencer_theorem_6_5
-- name    : FreeSpencer.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:54.461798+00:00
-- url     : https://prove2.me/theorems/81220856-c374-46a1-8c82-a22bd56ce54d
-- title:
--   Theorem 6.5, p.48 — the curvature estimate
-- statement:
--   Let $\ell\ge1$, let $0\preceq C\preceq I_\ell$, $\theta,L>0$, and let $E$ be the square potential. If the derivative in the covariance satisfies $\Gamma|_{\mathrm{ran}\,C}\preceq(L/\sqrt\ell)I$, then
--   $$\mathrm{Tr}(CJ)\le\Bigl(2+\frac{12\sqrt L}\theta\Bigr)\sqrt\ell,$$
--   and more generally, for every $c>0$,
--   $$\mathrm{Tr}(CJ)\le\Bigl(2+\frac{8\sqrt c+4L^2c^{-3/2}}\theta\Bigr)\sqrt\ell.$$
--   There is no hypothesis on the positive definiteness of $C$ or of $\eta_C(S)$. With $L=4096$, $\theta=128$ the coefficient is $8$. This is the estimate that controls the drift of the walk.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - encoding: J, Γ as derivatives (5.3); Tr(CJ) = Σₐ J(C^{1/2}eₐ, C^{1/2}eₐ) (p.31) → iterated deriv along lines of the potential, and the sum over the columns of MatrixLewis.mpow (1/2) C; reason: the same quantities; smoothness is in lemma_5_1 and theorem_D_1
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 6.5, p.48

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Theorem 6.5** (The curvature estimate), (6.20) and (6.21), for every covariance `0 ⪯ C ⪯ I_ℓ`,
including singular `C` and singular `η_C(S)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 6.5, p.48.

**Formalization Note** `J` and `Γ` are the derivatives (5.3) of the `sSup` potential along lines. With
`L = 4096`, `θ = 128` the coefficient is `8`, which is (3.2). -/
theorem theorem_6_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah)
    (hℓ : 1 ≤ ℓ) (θ L : ℝ) (hθ : 0 < θ) (hL : 0 < L) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : IsCov C)
    (hspike : NoSpike (1 / 2) θ 0 Ah H C (L / Real.sqrt ℓ)) :
    TrCJ (1 / 2) θ 0 Ah H C ≤ (2 + 12 * Real.sqrt L / θ) * Real.sqrt ℓ ∧
    ∀ c : ℝ, 0 < c →
      TrCJ (1 / 2) θ 0 Ah H C ≤
        (2 + (8 * Real.sqrt c + 4 * L ^ 2 * c ^ (-(3 / 2) : ℝ)) / θ) * Real.sqrt ℓ := by sorry

end FreeSpencer
