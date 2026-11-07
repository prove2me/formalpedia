-- Prove2me | Theorems.Thm_MFHeisGibbs_lemma_13
-- name    : MFHeisGibbs.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:29.126936+00:00
-- url     : https://prove2.me/theorems/cceab5c9-4528-4573-bdd1-688742d3887e
-- title:
--   Lemma 13, (69) — $\mathcal E_C(X)\ge\frac{2f(0)^2}n\sum_\alpha\|[S^\alpha_{\mathrm{tot}},X]\|_\rho^2$
-- statement:
--   Let $n\ge2$, let $\beta\ge0$ be finite, and let $f$ be continuous with the KMS relation. For every $X\in B(\mathcal H_n)$,
--
--   $$\mathcal E_C(X)\ge\frac{2f(0)^2}{n}\sum_{\alpha}\|[S^\alpha_{\mathrm{tot}},X]\|_\rho^2 .$$
--
--   Together with Lemma 14 this gives the bound $\Omega(1/n)$ outside $R_n$.
--
--   Differences from the source:
--   - encoding: f(0)² → ‖f 0‖²; reason: the KMS relation makes f(0) real, so these agree
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Lemma 13, (69), p.26 (PDF 27); again p.28 (PDF 29)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Lemma 13 (Collective comparison)**, (69), Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.26 (again
p.28): `E_C(X) ≥ (2f(0)²/n) ∑_α ∥[S^α_tot, X]∥²_ρ`, for `n ≥ 2`, finite `β ≥ 0`, `f` continuous with the
KMS relation.

**Formalization Note.** `f(0)` is real by the KMS relation, and `f(0)²` is written `‖f 0‖²`. -/
theorem lemma_13 (f : ℝ → ℂ) (hf : KMSRel f) (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (hn : 2 ≤ n) (X : Op n) :
    (2 * ‖f 0‖ ^ 2 / (n : ℝ)) * ∑ α : Fin 3, kmsNormSq β (comm (Stot n α) X) ≤
      dirichlet β (LC β f n) X := by sorry

end MFHeisGibbs
