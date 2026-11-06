-- Prove2me | Theorems.Thm_GuthMaynard_Affine_integral_mul_Hfun_le
-- name    : GuthMaynard.Affine.integral_mul_Hfun_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:46.481117+00:00
-- url     : https://prove2.me/theorems/99ce77ca-240e-4408-b25a-00a12b1581a7
-- title:
--   Cauchy–Schwarz step in Guth–Maynard Lemma 9.2 — ∫ f H ≤ (∫f²)^{1/2} J(g)^{1/2}, H the affine sum of g with |j| ≤ 8CM₂
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`Hfun`) and `GuthMaynard.J`. Let $C\ge1$, $0<M_2<M$, $f$ continuous with support in $[1/C,C]$, and $g$ continuous with $g\ge0$ and support in $[1/(2C),2C]$. Then
--
--   $$\int f(u)H(u)\,du\le\Big(\int f^2\Big)^{1/2}J_{M,8C}(g)^{1/2},$$
--
--   where $H$ = `Hfun C M₂ g` is $H(u)=\sum_{m_2,m_2'\sim M_2}\sum_{|j|\le8CM_2}g((m_2u+j)/m_2')$ and $J_{M,8C}(g)$ is `(J M (8 * C) g).toReal`.
--
--   A step in the proof of Guth–Maynard's Proposition 9.1 (Lemma 9.2 and its proof, arXiv:2405.20552v2 pp. 30–35); not a claim of the paper as stated.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 30–35, a step in the proof of Lemma 9.2 (used for Proposition 9.1)

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine

namespace GuthMaynard.Affine

open GuthMaynard MeasureTheory FourierTransform
open scoped ENNReal

theorem integral_mul_Hfun_le (C : ℝ) (hC : 1 ≤ C) (M M₂ : ℝ) (hM₂ : M₂ ∈ Set.Ioo 0 M)
    (f g : ℝ → ℝ) (hf : Continuous f) (hfs : Function.support f ⊆ Set.Icc (1 / C) C)
    (hg : Continuous g) (hgnn : ∀ u, 0 ≤ g u)
    (hgs : Function.support g ⊆ Set.Icc (1 / (2 * C)) (2 * C)) :
    ∫ u, f u * Hfun C M₂ g u ≤ √(∫ u, f u ^ 2) * √((J M (8 * C) g).toReal) := by
  sorry

end GuthMaynard.Affine
