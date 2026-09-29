-- Prove2me | Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
-- name    : ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/958e2dca-06e5-51c4-910b-e3e78e2222ad
-- title:
--   Attachment of the wide supersingular annulus to the zero chart
-- statement:
--   Fix a prime $p\ge 5$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $k$ has characteristic $p$ and is algebraically closed, let $\bar F_0$ be a field extension of $k$, and let $F=\overline{\mathbb Q}\cdot\mathbb Q(X_{\mathrm{full}}(1\cdot p))$ be the base change to $\overline{\mathbb Q}$, inside Laurent series, of the full modular function field of level $1\cdot p$. Given a component chart $C_0$ of $F$ over $A$ with residues in $\bar F_0$, a place $x_0$ of $\bar F_0$ over $k$ lying in $C_0.\mathrm{nodes}$, and $a\in k$ with $a\in\mathrm{ssJSet}\,p\,k$ (every elliptic curve over $k$ of $j$-invariant $a$ has no nonzero point killed by $p$), $a^{p^2}=a$ and $a=0$ or $a=1728$, suppose: $\mathrm{An}$ is an annulus over $A$ in $F$ with parameter $z$, whose domain consists exactly of the places $W$ for which some $x\in A$ with residue $a$ has $W.\mathrm{ord}(j_q-x)>0$ and some $y\in A$ with residue $a^p$ has $W.\mathrm{ord}(j_q(q^p)-y)>0$; the Fricke transform of $z$ lies in $\mathrm{modularLocalized}$ with nonzero reduction belonging to $\mathrm{modularFunctionFieldC}\,k\,1$ and of order $1$ at the place $\mathrm{charLGeomPlaceOfPoint}\,k\,(a^p)$; there is $z'$ with $z'z=p^{\,\mathrm{jWidth}\,a}$ ($=p^3$ if $a=0$, $p^2$ if $a=1728$) such that $z'$ itself lies in $\mathrm{modularLocalized}$ with nonzero reduction in $\mathrm{modularFunctionFieldC}\,k\,1$ of order $1$ at $\mathrm{charLGeomPlaceOfPoint}\,k\,a$; every $g\in F$ whose Fricke transform lies in $\mathrm{modularLocalized}$ with nonzero reduction lies in $C_0.\mathrm{integers}$ with nonzero $C_0$-residue; and for every $g\in C_0.\mathrm{integers}$ whose Fricke transform lies in $\mathrm{modularLocalized}$ with reduction in $\mathrm{modularFunctionFieldC}\,k\,1$, $x_0.\mathrm{ord}(C_0.\mathrm{residue}\,g)$ equals the order of that reduction at $\mathrm{charLGeomPlaceOfPoint}\,k\,(a^p)$. Then $\mathrm{An}$ is attached to $C_0$ at $x_0$: $x_0$ is a node of $C_0$, the parameter $z$ lies in $C_0.\mathrm{integers}$ and its residue has order $1$ at $x_0$, and for every $f\in C_0.\mathrm{integers}$ with nonzero residue and order $0$ at all places of $\mathrm{An}.\mathrm{dom}$ and every such place $P$, the element $P(f)\cdot P(z)^{-x_0.\mathrm{ord}(C_0.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there.
--
--   This is the wide-node case ($j$-invariant $0$ or $1728$, of width $3$ resp. $2$) of the dictionary matching a supersingular annulus of $X_0(p)$ in characteristic $p$ with the node of the chart of the component through the cusp $0$, the annulus parameter being the branch element of the crossing rather than $j_p-j^p$. It feeds the constructions of component charts and annuli for prolongation tuples and the corresponding existence statement for supersingular and opposite annuli at level $1\cdot p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type}
    [Field Fbar0]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodes0 : x0 ∈ C0.nodes)
    (An : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (z : ↥(modularFunctionFieldBar (1 * p)))
    (hz : An.param = z)
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))))
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * p) z : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (z' : ↥(modularFunctionFieldBar (1 * p)))
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (((p : ℕ) : AlgebraicClosure ℚ) ^ jWidth a))
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An.IsAttached C0 x0 := by sorry
