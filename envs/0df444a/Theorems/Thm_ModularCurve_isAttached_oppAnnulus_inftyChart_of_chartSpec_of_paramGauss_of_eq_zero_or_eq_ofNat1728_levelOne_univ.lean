-- Prove2me | Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
-- name    : ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/20e4d615-8073-5bc8-872f-e7b6c0f44613
-- title:
--   Attaching a wide supersingular annulus to the ∞-chart
-- statement:
--   Fix a prime $p\ge 5$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k$ has characteristic $p$, is algebraically closed and carries decidable equality, together with a field $F$ that is a $k$-algebra. Let $C$ be a `ComponentChart` for $A$ on the field $\overline{\mathbb{Q}}\cdot(\text{modular functions of level }1\cdot p)$, i.e. `modularFunctionFieldBar (1 * p)`, with residues in $F$, and let $x$ be a place of $F$ over $k$ lying in $C.\mathrm{nodes}$. Let $a\in k$ satisfy $a\in$ `ssJSet p k` (every elliptic curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point), $a^{p^2}=a$, and $a=0$ or $a=1728$. Let $\mathrm{An}'$ be an `Annulus` for $A$ on that field, with parameter $z'$, with $z'z$ equal to the image of the modulus for some $z$ in the field, with modulus $p^{\,e}$ where $e=$ `jWidth a` ($3$ if $a=0$, $2$ if $a=1728$), and whose domain consists exactly of the places $W$ at which both $j$ and the $p$-th $q$-expansion $j\circ q^{p}$ are congruent to elements of $A$ reducing to $a$ and to $a^{p}$ respectively, in the sense that $W.\mathrm{ord}$ of the corresponding difference is positive. Assume further: $z'$ lies in the localised modular ring `CharPReduction.modularLocalized` for the residue map of $A$, its reduction lies in `modularFunctionFieldC k 1`, is nonzero, and has order $1$ at the place `charLGeomPlaceOfPoint k a`; the same holds for `frickeInvolutionBar (1 * p) z` with the point $a^{p}$; every element of the field whose localised reduction is nonzero lies in $C.\mathrm{integers}$ with nonzero $C$-residue; and for every $g\in C.\mathrm{integers}$ whose localised reduction lies in `modularFunctionFieldC k 1`, the order of $C.\mathrm{residue}\,g$ at $x$ equals the order of that reduction at `charLGeomPlaceOfPoint k a`. The conclusion is $\mathrm{An}'.\mathrm{IsAttached}\ C\ x$: namely $x\in C.\mathrm{nodes}$, the parameter $z'$ lies in $C.\mathrm{integers}$ and its $C$-residue has order $1$ at $x$, and for every $f\in C.\mathrm{integers}$ with nonzero residue which has order $0$ at every place of the annulus domain, and every such place $P$, the element $P.\mathrm{evalAt}\,f\cdot(P.\mathrm{evalAt}\,z')^{-x.\mathrm{ord}(C.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there.
--
--   This is the wide-node case ($j=0$ or $1728$, of width $3$ resp. $2$) of the statement that a supersingular annulus of $X_0(p)$ over $\mathbb{Z}_p$ is attached, at the corresponding node, to the chart of the component through the cusp $\infty$, in the sense of the semistable chart/annulus formalism; the geometry behind it is the description of the supersingular crossings in Deligne–Rapoport. It feeds the construction of component charts and annuli for prolongation tuples in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ.lean

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

theorem ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type*}
    [Field Fbari]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodesi : xi ∈ Ci.nodes)
    (An' : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (z' z : ↥(modularFunctionFieldBar (1 * p)))
    (hz' : An'.param = z')
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((An'.modulus : ↥A) : AlgebraicClosure ℚ))
    (hmodw : An'.modulus = ((p : ℕ) : ↥A) ^ jWidth a)
    (hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An'.dom ↔
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
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * p) z : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (huniti : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An'.IsAttached Ci xi := by sorry
