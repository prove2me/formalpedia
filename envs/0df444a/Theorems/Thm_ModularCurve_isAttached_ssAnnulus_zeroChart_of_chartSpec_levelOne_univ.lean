-- Prove2me | Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ
-- name    : ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/fd3c9ca8-1d6e-5beb-b826-787e68722cc7
-- title:
--   Supersingular annulus attached to the zero chart, level 1· p
-- statement:
--   Let $p\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\bar F_0$ be a field over $\kappa$. Write $F=\mathtt{modularFunctionFieldBar}(1\cdot p)$, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot p$ inside Laurent series over $\overline{\mathbb Q}$, and let $j,\;j_p\in F$ be the coefficientwise images of `jq` and of its image under $q\mapsto q^{1\cdot p}$. Given a component chart $C_0$ of $F$ over $A$ valued in $\bar F_0$ (a valuation subring `integers` of $F$, a surjective residue map to $\bar F_0$ with kernel the maximal ideal, a set of places of $F/\overline{\mathbb Q}$, a finite node set of places of $\bar F_0/\kappa$ and a place map, subject to the structure's axioms), an element $X\in\bar F_0$ and a family $x(\cdot)$ of places of $\bar F_0/\kappa$ indexed by $\kappa$ such that $\mathrm{ord}_{x(c)}P(X)$ is the multiplicity of $c$ as a root of $P$ for all $c\in\kappa$ and all $P\in\kappa[T]$; assume $j,j_p$ lie in `C0.integers` with residues $X^p$ and $X$ respectively. Let $a\in\kappa$ satisfy: every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion point, $a^{p^2}=a$, $a\ne 0$, $a\ne 1728$, and $x(a^p)$ is a node of $C_0$. Let $An$ be an annulus over $A$ in $F$ whose parameter is $j_p-j^p$ and whose domain consists exactly of those places $W$ of $F/\overline{\mathbb Q}$ for which there are $x,y\in A$ with residues $a$ and $a^p$ and $\mathrm{ord}_W(j-x)>0$, $\mathrm{ord}_W(j_p-y)>0$. Assume finally the two dictionaries tying $C_0$ to the characteristic-$p$ reduction: every $g\in F$ whose Fricke involute lies in `CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)` and has nonzero image under `CharPReduction.modularRedLocHom` belongs to `C0.integers` with nonzero residue; and for $g\in$ `C0.integers` whose Fricke involute lies in that subring with reduction inside `modularFunctionFieldC` $\kappa\,1$, the order of `C0.residue` $g$ at $x(a^p)$ equals the order of that reduction at `charLGeomPlaceOfPoint` $\kappa\,(a^p)$. The conclusion is that $An$ is attached to $C_0$ at $x(a^p)$: that place is a node, the parameter $j_p-j^p$ lies in `C0.integers` and its residue has order $1$ at $x(a^p)$, and for every $f\in$ `C0.integers` with nonzero residue and order $0$ at all places of $An$'s domain and every such place $P$, the element $P(f)\cdot P(j_p-j^p)^{-\mathrm{ord}_{x(a^p)}(\text{residue of }f)}$ lies in $A$ and is a unit there.
--
--   This records the attachment of the supersingular annulus centred at a supersingular $j$-invariant $a$ to the component of the reduction of $X_0(p)$ carrying the coordinate $X$, in the Deligne–Rapoport picture of $X_0(p)$ in characteristic $p$ as two rational curves crossing at the supersingular points. It is the level-$1\cdot p$ form of [`ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ`](thm.html#ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ), stated with $\bar F_0$ in an arbitrary universe, and is used in the construction of component charts and annuli for a prolongation tuple arising from a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ.lean

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

open AlgebraicCurve IsLocalRing
open ModularCurve

theorem ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ
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
    (X : Fbar0)
    (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ C0.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ C0.integers)
    (hres_jp : C0.residue ⟨_, hjpF⟩ = X)
    (hres_j : C0.residue ⟨_, hjF⟩ = X ^ p)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0)
    (h1728 : a ≠ 1728)
    (hnodes0 : xpl (a ^ p) ∈ C0.nodes)
    (An : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (hparam : An.param = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p))
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
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        (xpl (a ^ p)).ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An.IsAttached C0 (xpl (a ^ p)) := by sorry
