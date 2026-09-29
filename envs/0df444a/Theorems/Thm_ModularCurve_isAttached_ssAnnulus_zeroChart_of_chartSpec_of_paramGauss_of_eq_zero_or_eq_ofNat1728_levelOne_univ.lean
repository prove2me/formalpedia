-- Prove2me | Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
-- name    : ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/72432b93-990c-54da-b7c2-2ee461af807c
-- title:
--   Attachment of a wide supersingular annulus to the zero chart
-- statement:
--   Let $p\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k=\mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed, and let $\overline{F}_0$ be a field extension of $k$. Write $F=\mathrm{modularFunctionFieldBar}(1\cdot p)$ for the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot p$ inside $\overline{\mathbb{Q}}((q))$. Let $C_0$ be a `ComponentChart` for $A$, $F$, $\overline{F}_0$ (a valuation subring $C_0.\mathrm{integers}$ of $F$, a surjective residue map to $\overline{F}_0$ with kernel the maximal ideal, a set $C_0.\mathrm{dom}$ of places of $F/\overline{\mathbb{Q}}$, a finite set $C_0.\mathrm{nodes}$ of places of $\overline{F}_0/k$, a place map, and the compatibility axioms of that structure), and let $x_0\in C_0.\mathrm{nodes}$. Let $a\in k$ satisfy $a\in \mathrm{ssJSet}\,p\,k$ (every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has trivial $p$-torsion in its group of affine points), $a^{p^2}=a$, and $a=0$ or $a=1728$. Let $\mathrm{An}$ be an `Annulus` for $A$ and $F$ with parameter $z=\mathrm{An}.\mathrm{param}$, and assume its domain is cut out by the crossing conditions: a place $W$ of $F/\overline{\mathbb{Q}}$ lies in $\mathrm{An}.\mathrm{dom}$ if and only if there are $x,y\in A$ with residues $a$ and $a^p$ respectively such that $W.\mathrm{ord}(j-x)>0$ and $W.\mathrm{ord}(j_p-y)>0$, where $j$ is the element of $F$ given by the $q$-expansion of the modular invariant and $j_p$ by its $p$-fold $q$-expansion rescaling. Assume further: the Fricke transform $\mathrm{frickeInvolutionBar}(1\cdot p)(z)$, as a Laurent series, lies in $\mathrm{modularLocalized}(1\cdot p)$ for $A$ and its residue map, its image under $\mathrm{modularRedLocHom}$ is a nonzero element of $\mathrm{modularFunctionFieldC}\,k\,1$ with order $1$ at the place $\mathrm{charLGeomPlaceOfPoint}\,k\,(a^p)$; there is $z'\in F$ with $z'z=p^{\mathrm{jWidth}\,a}$ (so the exponent is $3$ for $a=0$ and $2$ for $a=1728$) whose own reduction is a nonzero element of $\mathrm{modularFunctionFieldC}\,k\,1$ of order $1$ at $\mathrm{charLGeomPlaceOfPoint}\,k\,a$; every $g\in F$ whose Fricke transform has nonzero localized reduction lies in $C_0.\mathrm{integers}$ with $C_0.\mathrm{residue}\,g\neq 0$; and for every $g\in C_0.\mathrm{integers}$ whose Fricke transform reduces into $\mathrm{modularFunctionFieldC}\,k\,1$, the order of $C_0.\mathrm{residue}\,g$ at $x_0$ equals the order of that reduction at $\mathrm{charLGeomPlaceOfPoint}\,k\,(a^p)$. Then $\mathrm{An}.\mathrm{IsAttached}\,C_0\,x_0$: that is, $x_0\in C_0.\mathrm{nodes}$, the parameter $z$ lies in $C_0.\mathrm{integers}$ and its residue has order $1$ at $x_0$, and for every $f\in C_0.\mathrm{integers}$ with nonzero residue and with $P.\mathrm{ord}\,f=0$ for all $P\in\mathrm{An}.\mathrm{dom}$, the value $P.\mathrm{evalAt}\,f\cdot (P.\mathrm{evalAt}\,z)^{-x_0.\mathrm{ord}(C_0.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there, for every $P\in\mathrm{An}.\mathrm{dom}$.
--
--   This is the wide case ($j=0$ or $1728$, of width $3$ resp. $2$) of the statement that the supersingular annulus of $X_0(p)$ centred at a crossing $(a,a^p)$ is attached, at the node $x_0$, to the chart of the component through the cusp $0$: the annulus parameter specialises to a uniformiser of the node in that chart, and the slope law for units holds. It is used in assembling component charts and annuli into a model, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ.lean

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

theorem ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type*}
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
