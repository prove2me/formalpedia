-- Prove2me | Theorems.Thm_GuthMaynard_Affine_iteration
-- name    : GuthMaynard.Affine.iteration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:48.804028+00:00
-- url     : https://prove2.me/theorems/aeb9db52-5ba6-4055-a4ff-93cc0d4ac633
-- title:
--   Guth–Maynard Lemma 9.2 (iterative bound for J) — the affine sums of f are bounded by M⁶(∫f)² plus (M⁴∫f² · J(f̃))^{1/2}, with f̃ a smoothing of f in the class
-- statement:
--   Guth–Maynard's Lemma 9.2 (p. 30), in the form our proof of Proposition 9.1 uses. Notation from the bundle `Def_GuthMaynardAffine`: `gsum`, the hypothesis class `Adm C c T f`, and `GuthMaynard.J`.
--
--   Let $C\ge1$, $c:\mathbb N\times\mathbb R\to\mathbb R$, $K>0$ and $\eta>0$. Then there are $A$, $T_1$ and $c'$ such that for every $T\ge T_1$ and every $f$ with `Adm C c T f` there is a function $g$ with `Adm (2C) c' T g`, $\int g\le A\int f$ and $\int g^2\le A\int f^2$, such that for all $0<M\le T^6$ and $M_1,M_2,M_3\in(0,M)$
--
--   $$\int\mathrm{gsum}_{K,M_1,M_2,M_3}(f)(u)^2\,du\le A\,T^\eta\Big(M^6\Big(\int f\Big)^2+\Big(M^4\int f^2\cdot J_{M,8C}(g)\Big)^{1/2}\Big),$$
--
--   where $J_{M,8C}(g)$ is `(J M (8 * C) g).toReal` (so $0$ if $J$ is infinite).
--
--   The paper states the bound for $J(f)$ itself, with $\tilde f(u)=T\int\psi(T(u-u'))f(u')\,du'$ for a bump $\psi$, and leaves the class of $\tilde f$ to the proof of Proposition 9.1 (p. 31). Here $g$ is any function in the class with support constant $2C$ and comparable $L^1$ and $L^2$ norms (our proof takes $g=\tilde f$), the bound is stated for each triple $M_1,M_2,M_3$, it is restricted to $M\le T^6$ (the case $M\ge T^6$ is handled separately in our proof), and the right side has $J$ with $8C$ in place of $K$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 30, Lemma 9.2 (iterative bound for J), in the form used for Proposition 9.1

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine

namespace GuthMaynard.Affine

open GuthMaynard MeasureTheory FourierTransform
open scoped ENNReal

theorem iteration (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) (η : ℝ) (hη : 0 < η) :
    ∃ (A T₁ : ℝ) (c' : ℕ → ℝ → ℝ), ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∃ g : ℝ → ℝ, Adm (2 * C) c' T g ∧ (∫ u, g u) ≤ A * ∫ u, f u ∧
        (∫ u, g u ^ 2) ≤ A * ∫ u, f u ^ 2 ∧
        ∀ M : ℝ, 0 < M → M ≤ T ^ 6 →
        ∀ M₁ M₂ M₃ : ℝ, M₁ ∈ Set.Ioo 0 M → M₂ ∈ Set.Ioo 0 M → M₃ ∈ Set.Ioo 0 M →
        ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
          ENNReal.ofReal (A * T ^ η * (M ^ 6 * (∫ u, f u) ^ 2 +
            Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * (J M (8 * C) g).toReal))) := by
  sorry

end GuthMaynard.Affine
