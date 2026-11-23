-- Prove2me | Theorems.Thm_LeJEPAWorldModel_gaussian_of_affine_eigenfunction
-- name    : LeJEPAWorldModel.gaussian_of_affine_eigenfunction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:17:44.303263+00:00
-- url     : https://prove2.me/theorems/330d78a3-2c5a-4462-93e9-924e2130eafe
-- title:
--   Theorem 2 (as proved): an affine Sturm–Liouville eigenfunction forces a Gaussian density
-- statement:
--   Let $K>0$, and let $p:\mathbb R\to(0,\infty)$ be a differentiable probability density, $\int p=1$. Let $\mathcal D\varphi=\frac1p\frac{d}{dz}\big[Kp\,\varphi'\big]$ be the Sturm–Liouville generator (30). Suppose that the non-constant affine function $\varphi(z)=az+b$, $a\ne0$, is an eigenfunction of $\mathcal D$ with eigenvalue $\lambda>0$, meaning $\mathcal D\varphi=-\lambda\varphi$ on $\mathbb R$. Then $p$ is the Gaussian density with mean $-b/a$ and variance $K/\lambda$:
--
--   $$p(z)=\sqrt{\frac{\lambda}{2\pi K}}\exp\Big(-\frac{\lambda}{2K}\Big(z+\frac ba\Big)^2\Big)\quad\text{for all }z\in\mathbb R.$$
--
--   This is the argument of Appendix B.2 for Gaussian uniqueness: an affine eigenfunction forces the score $(\log p)'$ to be affine, and an affine score forces a Gaussian.
--
--   **Formalization Note** This is Theorem 2 as proved, not as printed. The printed Theorem 2 assumes that every whitened minimizer of the alignment loss is linear and concludes that $z$ is Gaussian. As printed it is false: a Rademacher latent with $N=1$ satisfies its hypotheses. This holds for the formula the theorem cites (eq. (3), which has no minimizer once a nonzero mean is allowed, so the hypothesis holds vacuously) and for the intended mean-zero reading. If one instead minimizes $\mathbb E\|h(z')-h(z)\|^2$ with no mean constraint, shifting a minimizer by a constant gives a non-linear minimizer, so the hypothesis fails whenever a minimizer exists. Its proof establishes only the implication stated here, in which the eigenfunction property is the hypothesis. The variance $K/\lambda$ is read off from the integrated equation (33).
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Section 4.2, Theorem 2, p. 6; the statement proved in Appendix B.2, eqs. (30)-(33), p. 23

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

theorem gaussian_of_affine_eigenfunction (K lam a b : ℝ) (hK : 0 < K) (hlam : 0 < lam)
    (ha : a ≠ 0) (p : ℝ → ℝ) (hpos : ∀ x, 0 < p x) (hdiff : Differentiable ℝ p)
    (hnorm : ∫ x, p x = 1)
    (heig : ∀ x, slGenerator K p (fun y => a * y + b) x = -lam * (a * x + b)) :
    ∀ x, p x = gaussianPDFReal (-b / a) (K / lam).toNNReal x := by sorry

end LeJEPAWorldModel
