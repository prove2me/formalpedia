-- Prove2me | Theorems.Thm_GuthMaynard_Affine_lintegral_W_sq_low
-- name    : GuthMaynard.Affine.lintegral_W_sq_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:43.337205+00:00
-- url     : https://prove2.me/theorems/35ea463a-8d1a-4174-af2a-62a98d29f382
-- title:
--   Low frequencies in Guth–Maynard Lemma 9.2 — on |ξ| ≤ T²⁰, ∫W² is O(T^{3η}M⁶(∫f)²) plus twice the integral of Wnear² over region II
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`Wfun`, `Wnear`, `regII`, `Adm`, `Regime`). Let $C\ge1$, $c$, $K>0$ and $\eta>0$. Then there are $A\ge0$ and $T_1$ such that for every $T\ge T_1$, every $f$ with `Adm C c T f` and all $M,M_1,M_2,M_3$ with `Regime T M M₁ M₂ M₃`,
--
--   $$\int_{|\xi|\le T^{20}}W(\xi)^2\,d\xi\le A\,T^{3\eta}M^6\Big(\int f\Big)^2+2\int_{\mathrm{II}}W_{\rm near}(\xi)^2\,d\xi,$$
--
--   where $W$ = `Wfun K M₁ M₂ M₃ f`, $W_{\rm near}$ = `Wnear K M₁ M₂ M₃ (T^η) f`, and $\mathrm{II}$ = `regII T η M₁ M₃` is the set $4T^\eta M_1/M_3<|\xi|\le T^{20}$ (the integrals are of extended nonnegative reals).
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

theorem lintegral_W_sq_low (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K)
    (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ T ^ 20}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
          ENNReal.ofReal (A * (T ^ η) ^ 3 * M ^ 6 * (∫ u, f u) ^ 2) +
            2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ (T ^ η) f ξ ^ 2) := by
  sorry

end GuthMaynard.Affine
