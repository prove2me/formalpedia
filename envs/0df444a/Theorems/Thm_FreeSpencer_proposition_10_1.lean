-- Prove2me | Theorems.Thm_FreeSpencer_proposition_10_1
-- name    : FreeSpencer.proposition_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:48.396203+00:00
-- url     : https://prove2.me/theorems/cb3e201f-0d48-4470-92d5-50ee7aa856a9
-- title:
--   Proposition 10.1, p.63 — the rectangular curvature estimate
-- statement:
--   Let $q=1/p$ with integer $p\ge2$, $\theta,L>0$, $\kappa\ge0$, and let $E_\kappa$ be the potential (10.1). At every covariance $0\preceq C\preceq I_\ell$, $\ell\ge1$, including singular ones,
--   $$\Gamma_\kappa|_{\mathrm{ran}\,C}\preceq\frac L{\sqrt\ell}I\implies\mathrm{Tr}(CJ_\kappa)\le2\sqrt\ell+\frac{6L^q}{\theta q}\ell^{1-q}=:B_\ell\sqrt\ell.$$
--   At $q=1/2$ this is (6.20).
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - generalization: κ > 0 in (10.1) → κ ≥ 0; reason: κ = 0 is Theorem 9.5 with Proposition 9.6 (p.63), so the case holds, and this specializes to the source
--   - encoding: J, Γ as derivatives (5.3); Tr(CJ) = Σₐ J(C^{1/2}eₐ, C^{1/2}eₐ) (p.31) → iterated deriv along lines of the potential, and the sum over the columns of MatrixLewis.mpow (1/2) C; reason: the same quantities; smoothness is in lemma_5_1 and theorem_D_1
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Proposition 10.1, p.63

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Proposition 10.1** (The same response bound at the new optimizer), (10.3).
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Proposition 10.1, p.63.

**Formalization Note** The page has `κ > 0`; `κ = 0` is Theorem 9.5 with Proposition 9.6 (p.63), so `κ ≥ 0`
is stated, which specializes to the page. `B_ℓ` is only a name for the coefficient. At `q = 1/2` the
bound is (6.20). -/
theorem proposition_10_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah)
    (hℓ : 1 ≤ ℓ) (p : ℕ) (hp : 2 ≤ p) (θ κ L : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ) (hL : 0 < L)
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : IsCov C)
    (hspike : NoSpike (1 / (p : ℝ)) θ κ Ah H C (L / Real.sqrt ℓ)) :
    TrCJ (1 / (p : ℝ)) θ κ Ah H C ≤
      2 * Real.sqrt ℓ + 6 * L ^ (1 / (p : ℝ)) / (θ * (1 / (p : ℝ))) * (ℓ : ℝ) ^ (1 - 1 / (p : ℝ)) := by sorry

end FreeSpencer
