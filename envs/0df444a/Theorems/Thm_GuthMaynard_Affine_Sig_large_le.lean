-- Prove2me | Theorems.Thm_GuthMaynard_Affine_Sig_large_le
-- name    : GuthMaynard.Affine.Sig_large_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:40.240487+00:00
-- url     : https://prove2.me/theorems/ffca12cd-dae1-4605-a84e-7574b01714da
-- title:
--   Large ℓ in Guth–Maynard Lemma 9.2 — the part of Σ with |ℓ| > T^{1+η}/M₂ is O(M⁴(∫f)²)
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`SigLarge`, `Adm`, `Regime`). Let $C\ge1$, $c$ and $\eta>0$. Then there are $A\ge0$ and $T_1$ such that for every $T\ge T_1$, every $f$ with `Adm C c T f` and all $M,M_1,M_2,M_3$ with `Regime T M M₁ M₂ M₃`,
--
--   $$\sum_{|\ell|>T^{1+\eta}/M_2}\ \int_{|\tau|\le T^\eta,\ |\ell+\tau/M_3|\ge2T^\eta/M_3}|\Gamma(\ell+\tau/M_3)|^2\,d\tau\le A\,M^4\Big(\int f\Big)^2,$$
--
--   where $\Gamma(y)=\sum_{m_2\sim M_2}m_2\widehat f(m_2y)$; the left side is `SigLarge (T^(1+η)/M₂) (T^η) M₂ M₃ f` (with $\ell\ne0$, an extended nonnegative real).
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

theorem Sig_large_le (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        SigLarge (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f ≤
          ENNReal.ofReal (A * M ^ 4 * (∫ u, f u) ^ 2) := by
  sorry

end GuthMaynard.Affine
