-- Prove2me | Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_univ
-- name    : ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/aeb3a701-7698-544f-a5fa-072c5adff95d
-- title:
--   Attachment of the supersingular annulus to the zero chart
-- statement:
--   Let $p\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k$ is algebraically closed of characteristic $p$, and let $Fbar0$ be a field over $k$. Let $C_0$ be a component chart for $A$ on the geometric modular function field $F_p=\overline{\mathbb{Q}}\cdot\mathrm{modularFunctionFieldFull}\,p$ inside Laurent series, with values in $Fbar0$; let $X\in Fbar0$ and let $c\mapsto xpl(c)$ assign to each $c\in k$ a place of $Fbar0/k$ such that $xpl(c).\mathrm{ord}$ of $P(X)$ equals the multiplicity of $c$ as a root of $P$, for every $P\in k[T]$. Assume the images $j$ and $j_p=\mathrm{qExpand}_p\,j$ of the classical $j$-series lie in $C_0.\mathrm{integers}$ with residues $X$ and $X^{p}$ respectively. Let $a\in k$ satisfy: every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no affine $p$-torsion point besides the origin; $a^{p^2}=a$; $a\ne 0$; $a\ne 1728$; and $xpl(a^{p})\in C_0.\mathrm{nodes}$. Let $An$ be an annulus for $A$ on $F_p$ whose parameter is $j_p-j^{p}$ and whose domain consists exactly of the places $W$ for which $W.\mathrm{ord}(j-x)>0$ and $W.\mathrm{ord}(j_p-y)>0$ for some $x,y\in A$ reducing to $a$ and $a^{p}$. Assume finally the two comparison hypotheses relating $C_0$ to the localized characteristic-$p$ reduction along the cusp: first, if $g\in F_p$ has Fricke transform `frickeInvolutionBar p g` lying in `CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue A)` with nonzero image under `CharPReduction.modularRedLocHom`, then $g\in C_0.\mathrm{integers}$ with nonzero residue; second, if in addition $g\in C_0.\mathrm{integers}$ and that image lies in $\mathrm{modularFunctionFieldC}\,k\,1$, then the order of $C_0.\mathrm{residue}\,g$ at $xpl(a^{p})$ equals the order of the image at `charLGeomPlaceOfPoint k (a ^ p)`. Then $An$ is attached to $C_0$ at $xpl(a^{p})$: this place is a node of $C_0$, the parameter $j_p-j^{p}$ lies in $C_0.\mathrm{integers}$ and its residue has order $1$ at $xpl(a^{p})$, and for every $f\in C_0.\mathrm{integers}$ with nonzero residue and with $P.\mathrm{ord}\,f=0$ for all $P\in An.\mathrm{dom}$, one has for each such $P$ that $P.\mathrm{evalAt}\,f\cdot(P.\mathrm{evalAt}(j_p-j^{p}))^{-m}$ lies in $A$ and is a unit there, where $m$ is the order at $xpl(a^{p})$ of the residue of $f$.
--
--   This is the attachment, at the end lying on the component through the cusp $0$, of a supersingular annulus of $X_0(p)$ over $A$ to the chart of that component: the annulus parameter $j(q^p)-j(q)^p$ is a local coordinate with a simple zero at the node $xpl(a^{p})$, and the slope of any chart unit along the annulus is read off from the order of its residue at that node. It feeds the corresponding level-one statement [`ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ`](thm.html#ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ) in the semistable-reduction analysis of $X_0(p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_univ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type*} [Field Fbar0] [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar p) Fbar0)
    (X : Fbar0) (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)) ∈ C0.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p)) ∈ C0.integers)
    (hres_jp : C0.residue ⟨_, hjpF⟩ = X) (hres_j : C0.residue ⟨_, hjF⟩ = X ^ p)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (hnodes0 : xpl (a ^ p) ∈ C0.nodes)
    (An : Annulus A ↥(modularFunctionFieldBar p))
    (hparam : An.param = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (y : AlgebraicClosure ℚ)))))
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        (xpl (a ^ p)).ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An.IsAttached C0 (xpl (a ^ p)) := by sorry
