-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_7_9
-- name    : OptimalSpectrum.Entangled.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:07.186817+00:00
-- url     : https://prove2.me/theorems/b8808f8b-dc05-4e43-ba76-7584de3781c6
-- title:
--   Lemma 7.9 — Hilbert–Schmidt bounds for the derivative operators
-- statement:
--   Let $p$ be a real polynomial of degree at most $k$ and let $0\preceq\sigma\preceq LI_d$ with $\mathrm{tr}\,\sigma\le1$. For every $1\le r\le k$, the derivative operator $\Theta^{(r)}_p$ of Eq. (40) satisfies
--
--   $$\big\|\Theta^{(r)}_p\big\|_{\mathrm{HS}}^2\le\frac{d^{\uparrow r}}{(r-1)!}\|p^{(r)}\|_{\infty,[0,L]}^2,\qquad \big\|\Theta^{(r)}_p(\sqrt\sigma)^{\otimes r}\big\|_{\mathrm{HS}}^2\le\frac{\prod_{j=0}^{r-1}(1+jL)}{(r-1)!}\|p^{(r)}\|_{\infty,[0,L]}^2 .$$
--
--   Combined with Lemma 7.3 this gives the polynomial variance bound of Lemma 7.1; the second bound has no dimension factor, which is the source of the entangled scheme's advantage.
--
--   Differences from the source:
--   - encoding: "the derivative operator Θ_p^(r) in Eq. (40)" → any Θ satisfying Eq. (40) at σ for all Hermitian directions; reason: Eq. (40) determines it uniquely
--   - encoding: d^↑r and √σ → ∏_(j<r)(d + j) and the functional-calculus square root; reason: notation
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.9, p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily
import Definitions.Def_OptimalSpectrum_Entangled_derivOp
import Definitions.Def_OptimalSpectrum_Entangled_hsNormSq
import Definitions.Def_OptimalSpectrum_Entangled_supNormDeriv

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace OptimalSpectrum.Entangled

/-- **Lemma 7.9 (Bounds for the derivative operators).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.9, printed p. 25 (PDF p. 27): "Let p be a polynomial of degree at most k, and let
0 ⪯ σ ⪯ LI_d with tr(σ) ⩽ 1. For every 1 ⩽ r ⩽ k, the derivative operator Θ_p^(r) in Eq. (40)
satisfies ∥Θ_p^(r)∥²_HS ⩽ (d^↑r/(r − 1)!) ∥p^(r)∥²_(∞,[0,L]),
∥Θ_p^(r)(√σ)^⊗r∥²_HS ⩽ (∏_(j=0)^(r−1)(1 + jL)/(r − 1)!) ∥p^(r)∥²_(∞,[0,L])."

**Formalization Note.** `σ` is any such PSD matrix (not necessarily diagonal). `Θ` is any operator
satisfying Eq. (40) at `σ` for all Hermitian directions (it is unique). `d^↑r` is written
`∏_(j<r)(d + j)`. `√σ` is the continuous-functional-calculus square root. -/
theorem lemma_7_9 (d k : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ k) (L : ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef)
    (hσL : ((L : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - σ).PosSemidef)
    (htr : (Matrix.trace σ).re ≤ 1) (r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k)
    (Θ : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hΘ : ∀ H : Fin r → Matrix (Fin d) (Fin d) ℂ, (∀ j, (H j).IsHermitian) →
      Matrix.trace (Θ * kronFamily H) = (derivOp p σ r H : ℂ)) :
    hsNormSq Θ ≤
        (∏ j ∈ Finset.range r, ((d : ℝ) + j)) / ((r - 1).factorial : ℝ) * supNormDeriv p r L ^ 2 ∧
    hsNormSq (Θ * QAlgorithms.piKron r (CFC.sqrt σ)) ≤
        (∏ j ∈ Finset.range r, (1 + (j : ℝ) * L)) / ((r - 1).factorial : ℝ) *
          supNormDeriv p r L ^ 2 := by sorry

end OptimalSpectrum.Entangled
