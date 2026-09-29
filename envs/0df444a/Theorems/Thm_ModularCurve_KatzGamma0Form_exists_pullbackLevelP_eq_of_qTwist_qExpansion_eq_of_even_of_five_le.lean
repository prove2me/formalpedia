-- Prove2me | Theorems.Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
-- name    : ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9e05534c-a9c0-5077-9d06-e96be4d07e25
-- title:
--   Level reduction for even-weight Katz forms on Γ₀(p)
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime with $5 \le p$ and $p$ invertible in $R$, and $k$ an even integer. Let $\varphi$ be a Katz $\Gamma_0(p)$-form of weight $k$ over $R$: a rule assigning to every $R$-algebra $A$, every Weierstrass curve $W$ over $A$ with unit discriminant and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ in $A$ that is a level-$p$ structure (both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine equation of $W$, both $x_P$ and $x_Q$ are roots of $W.\mathrm{pre}\Psi_p$, and the two elements $\mathrm{indepElt}\,W\,p\,x_P\,x_Q=\prod_{a=1}^{(p-1)/2}(x_Q\Psi_a^2(x_P)-\Phi_a(x_P))$ and $\mathrm{indepElt}\,W\,p\,x_Q\,x_P$ are units) an element of $A$, compatibly with $R$-algebra maps, scaling by $u^{-k}$ under a variable change with scaling factor $u$, and depending on $D$ only through the line of $x_Q$ in the sense of `InLine`. Over $R_1=\mathrm{AdjoinRoot}(\Phi_p)$ with $\zeta$ the class of the root, consider the curve $\mathrm{tateBase}$ over $R_1((q))$ (the formal Tate curve pulled back along $q \mapsto q^p$) with the cusp data given by the toric point at $\zeta$ and the non-toric point at $(1,1)$; assume this quadruple is a level-$p$ structure, and assume the resulting Laurent series $\varphi_\infty$ is fixed by the twist $q \mapsto \zeta q$ (coefficientwise multiplication of the $n$-th coefficient by $\zeta^n$). Then there is a level-one Katz modular form $g$ of weight $k$ over $R$ whose pullback to level $p$ (evaluate $g$ on $W$, ignoring the level structure) equals the underlying level-$p$ form of $\varphi$.
--
--   This is the reduction-of-level statement of Mazur (Modular curves and the Eisenstein ideal, II, Lemma 5.9) in Katz's functorial language: a $\Gamma_0(p)$-form whose expansion at Mazur's cusp is a Laurent series in $q^p$ descends to level one. It is used in the project's results on $q$-expansions of Katz forms, namely the divisibility statement for $12 a_0$ and the $a_n$, and the construction of a Katz form with prescribed constant $q$-expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) {k : ℤ} (hk : Even k)
    (φ : ModularCurve.KatzGamma0Form R p k)
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase (ModularCurve.cyclRing R p) p) p
      (ModularCurve.cuspData (ModularCurve.cyclRing R p) p (ModularCurve.cyclZeta R p) ![1, 0] ![0, 1]))
    (hσ : ModularCurve.qTwist (ModularCurve.cyclZeta R p)
        (φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc)
      = φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc) :
    ∃ g : KatzModularForm R k, g.pullbackLevelP p = φ.toKatzLevelPForm := by sorry
