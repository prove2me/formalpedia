-- Prove2me | Theorems.Thm_GuthMaynard_Affine_lintegral_Wnear_sq_le_Sig
-- name    : GuthMaynard.Affine.lintegral_Wnear_sq_le_Sig
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:37.467204+00:00
-- url     : https://prove2.me/theorems/241ccb0b-1569-4e66-aa8d-1a22e0f04bef
-- title:
--   The near part in Guth–Maynard Lemma 9.2 — the integral of Wnear² over region II is O(T^{2η} M Σ)
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`Wnear`, `regII`, `Sig`, `Adm`, `Regime`). Let $C\ge1$, $c$, $K>0$ and $\eta>0$. Then there are $A\ge0$ and $T_1$ such that for every $T\ge T_1$, every $f$ with `Adm C c T f` and all $M,M_1,M_2,M_3$ with `Regime T M M₁ M₂ M₃`,
--
--   $$\int_{\mathrm{II}}W_{\rm near}(\xi)^2\,d\xi\le A\,T^{2\eta}M\cdot\Sigma,$$
--
--   where $W_{\rm near}$ = `Wnear K M₁ M₂ M₃ (T^η) f`, $\mathrm{II}$ = `regII T η M₁ M₃` is the set $4T^\eta M_1/M_3<|\xi|\le T^{20}$, and $\Sigma$ = `Sig (T^η) M₂ M₃ f` $=\sum_{\ell\ne0}\int_{|\tau|\le T^\eta,\ |\ell+\tau/M_3|\ge2T^\eta/M_3}|\Gamma(\ell+\tau/M_3)|^2\,d\tau$ with $\Gamma(y)=\sum_{m_2\sim M_2}m_2\widehat f(m_2y)$ (extended nonnegative reals).
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

theorem lintegral_Wnear_sq_le_Sig (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K)
    (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ (T ^ η) f ξ ^ 2) ≤
          ENNReal.ofReal (A * (T ^ η) ^ 2 * M) * Sig (T ^ η) M₂ M₃ f := by
  sorry

end GuthMaynard.Affine
