-- Prove2me | Theorems.Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
-- name    : ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/396b1ead-8a6a-5816-b638-ee5bd53dad3f
-- title:
--   Level reduction for Katz Γ₀(p) forms, p≥ 5
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime with $5 \le p$ and $p$ invertible in $R$, and $k$ an integer. Let $\varphi$ be a `KatzGamma0Form R p k`: a rule assigning to every $R$-algebra $A$, every Weierstrass curve $W$ over $A$ with unit discriminant and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ in $A$ satisfying `IsLevelPStructure` (both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine equation of $W$, $x_P$ and $x_Q$ are roots of $W.\mathrm{pre}\Psi_p$, and the two elements $\mathrm{indepElt}\,W\,p\,x_P\,x_Q$, $\mathrm{indepElt}\,W\,p\,x_Q\,x_P$ are units) an element of $A$, compatibly with $R$-algebra maps, transforming by $u^{-k}$ under a variable change with unit scaling $u$, and depending only on the second line, in the sense that the value is unchanged when $x_Q$ is replaced by any $x_{Q'}$ with `InLine`. Put $R_1 = R[X]/(\Phi_p)$ with $\zeta =$ `cyclZeta`, and consider over $R_1((q))$ the Tate curve pulled back along $q \mapsto q^p$, `tateBase`, with the level-$p$ data `cuspData` attached to $v = (1,0)$ and $w = (0,1)$, namely the toric point at $\zeta$ together with the $q$-point (Mazur's cusp); that this quadruple is a level-$p$ structure is assumed as a hypothesis. Assume the value of $\varphi$ on this datum is invariant under `qTwist` $\zeta$, the ring endomorphism of $R_1((q))$ multiplying the $n$-th coefficient by $\zeta^n$, i.e. under $q \mapsto \zeta q$. Then there exists a level-one Katz modular form $g$ of weight $k$ over $R$ whose pullback `pullbackLevelP p`, which evaluates $g$ on the curve and ignores the level structure, equals the underlying level-$p$ form of $\varphi$. Only existence is asserted, not uniqueness.
--
--   This is the level-reduction step in the form of Mazur's Lemma II.5.9 in the Eisenstein ideal paper: a Katz form on $\Gamma_0(p)$ whose expansion at Mazur's cusp is a Laurent series in $q^p$ descends to level one. It is the edition for $p \ge 5$, where the required torsion information for the formal Tate curve is available, and is instantiated by the even-weight version used in the constant-term computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) {k : ℤ}
    (φ : ModularCurve.KatzGamma0Form R p k)
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase (ModularCurve.cyclRing R p) p) p
      (ModularCurve.cuspData (ModularCurve.cyclRing R p) p (ModularCurve.cyclZeta R p) ![1, 0] ![0, 1]))
    (hσ : ModularCurve.qTwist (ModularCurve.cyclZeta R p)
        (φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc)
      = φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc) :
    ∃ g : KatzModularForm R k, g.pullbackLevelP p = φ.toKatzLevelPForm := by sorry
