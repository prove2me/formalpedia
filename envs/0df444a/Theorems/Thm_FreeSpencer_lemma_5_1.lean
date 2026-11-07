-- Prove2me | Theorems.Thm_FreeSpencer_lemma_5_1
-- name    : FreeSpencer.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:42.894346+00:00
-- url     : https://prove2.me/theorems/42096399-5dcc-43b7-b341-74fb37792209
-- title:
--   Lemma 5.1, p.30 — smoothness on a coefficient face, density floor
-- statement:
--   Let $V\subseteq\mathbb R^\ell$ be a subspace, the range of an isometry $W$, and let $C=WC_0W^T$ with $C_0\succ0$; these are the covariances positive definite on $V$ and zero on $V^\perp$. For the square potential at $\theta>0$ and any symmetric $H$, the maximum defining $E(H,C)$ is attained by a unique density $S$, which is positive definite, and with $v=\|\eta_C(I)\|_{op}$,
--   $$S\succeq\frac{\theta^2}{(2\|H\|_{op}+2\sqrt v+\theta\sqrt D)^2}I.$$
--   Moreover $S(H,C)$ and $E(H,C)$ are smooth in $(H,C_0)$ on the open face. This allows $\eta_C(S)$ to be singular on $\mathbb R^D$, and it is what gives meaning to the derivatives $J$ and $\Gamma$.
--
--   **Formalization Note** Smoothness is $C^\infty$ at each symmetric $H$ and $C_0\succ0$, in the full matrix spaces through the symmetric part of the two arguments.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - encoding: C positive definite on V and zero on V⊥; smooth dependence in the relative open face → C = W C₀ Wᵀ with W an isometry onto V and C₀ ≻ 0; ContDiffAt ℝ ∞ through symPart; reason: the same set of covariances; a ContDiffOn on the thin face would not pin down the derivative
--   - encoding: a maximum over densities → sSup over densities; reason: attainment is proved in lemma_5_1 (Lemma 4.4); the set is nonempty and bounded
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.1, p.30; Lemma 4.4, p.28

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace FreeSpencer

/-- **Lemma 5.1** (Smoothness on a coefficient face and a density floor), with the attainment and
uniqueness of Lemma 4.4. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.1, p.30; Lemma 4.4, p.28.

**Formalization Note** The face `V` is the range of an isometry `W : ℝ^r → ℝ^ℓ`, and `C = W C₀ Wᵀ` with
`C₀ ≻ 0` on `ℝ^r`, which is every `C` positive definite on `V` and zero on `V^⊥`. Smoothness is
`C^∞` of `(H, C₀) ↦ S(H, C), E(H, C)`, at interior points of the open symmetric face, through the
symmetric part (`symPart`) of the two arguments. The case `r = 0` is `C = 0`. `η_C(S)` may be singular,
as the page says. The potential is the square one `(q, κ) = (1/2, 0)`. The contraction hypothesis is
the standing one of Section 2. -/
theorem lemma_5_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ r : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (θ : ℝ)
    (hθ : 0 < θ) (W : Matrix (Fin ℓ) (Fin r) ℝ) (hW : Wᵀ * W = 1) :
    (∀ (H : Matrix ι ι ℝ) (C₀ : Matrix (Fin r) (Fin r) ℝ), H.IsSymm → C₀.PosDef →
      ∃ S : Matrix ι ι ℝ, S.PosDef ∧ IsMaximizer (1 / 2) θ 0 Ah H (W * C₀ * Wᵀ) S ∧
        (∀ S', IsMaximizer (1 / 2) θ 0 Ah H (W * C₀ * Wᵀ) S' → S' = S) ∧
        pot (1 / 2) θ 0 Ah H (W * C₀ * Wᵀ) = potObj (1 / 2) θ 0 Ah H (W * C₀ * Wᵀ) S ∧
        (S - (θ ^ 2 / (2 * ‖H‖ + 2 * Real.sqrt ‖covMap Ah (W * C₀ * Wᵀ) 1‖ +
          θ * Real.sqrt (Fintype.card ι)) ^ 2) • (1 : Matrix ι ι ℝ)).PosSemidef) ∧
    (∀ (H : Matrix ι ι ℝ) (C₀ : Matrix (Fin r) (Fin r) ℝ), H.IsSymm → C₀.PosDef →
      ContDiffAt ℝ ∞ (fun p : Matrix ι ι ℝ × Matrix (Fin r) (Fin r) ℝ =>
        optDensity (1 / 2) θ 0 Ah (symPart p.1) (W * symPart p.2 * Wᵀ)) (H, C₀) ∧
      ContDiffAt ℝ ∞ (fun p : Matrix ι ι ℝ × Matrix (Fin r) (Fin r) ℝ =>
        pot (1 / 2) θ 0 Ah (symPart p.1) (W * symPart p.2 * Wᵀ)) (H, C₀)) := by sorry

end FreeSpencer
