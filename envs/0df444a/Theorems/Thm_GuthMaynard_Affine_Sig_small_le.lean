-- Prove2me | Theorems.Thm_GuthMaynard_Affine_Sig_small_le
-- name    : GuthMaynard.Affine.Sig_small_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:50.817193+00:00
-- url     : https://prove2.me/theorems/006592c0-f644-4d54-8df1-f481e9b6858d
-- title:
--   Small ℓ in Guth–Maynard Lemma 9.2 — the part of Σ with 1 ≤ |ℓ| ≤ T^{1+η}/M₂ is O(T^{2η} M₂ ∫ f H + T^η M⁴(∫f)²), H the affine sum of the smoothing
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`SigSmall`, `Hfun`, `smooth`, `Adm`, `Regime`). Let $C\ge1$, $c$ and $\eta>0$. Then there are $A\ge0$ and $T_1$ such that for every $T\ge T_1$, every $f$ with `Adm C c T f` and all $M,M_1,M_2,M_3$ with `Regime T M M₁ M₂ M₃`,
--
--   $$\sum_{0<|\ell|\le T^{1+\eta}/M_2}\ \int_{|\tau|\le T^\eta,\ |\ell+\tau/M_3|\ge2T^\eta/M_3}|\Gamma(\ell+\tau/M_3)|^2\,d\tau\le A\,T^{2\eta}M_2\int f(u)H(u)\,du+A\,T^\eta M^4\Big(\int f\Big)^2,$$
--
--   where $\Gamma(y)=\sum_{m_2\sim M_2}m_2\widehat f(m_2y)$, $\tilde f$ = `smooth T f` is $\tilde f(x)=T\int\beta(T(x-y))f(y)\,dy$, and $H$ = `Hfun C M₂ f̃` is $H(u)=\sum_{m_2,m_2'\sim M_2}\sum_{|j|\le8CM_2}\tilde f((m_2u+j)/m_2')$; the left side is `SigSmall (T^(1+η)/M₂) (T^η) M₂ M₃ f` (an extended nonnegative real).
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

theorem Sig_small_le (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        SigSmall (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f ≤
          ENNReal.ofReal (A * (T ^ η) ^ 2 * M₂ * (∫ u, f u * Hfun C M₂ (smooth T f) u) +
            A * T ^ η * M ^ 4 * (∫ u, f u) ^ 2) := by
  sorry

end GuthMaynard.Affine
