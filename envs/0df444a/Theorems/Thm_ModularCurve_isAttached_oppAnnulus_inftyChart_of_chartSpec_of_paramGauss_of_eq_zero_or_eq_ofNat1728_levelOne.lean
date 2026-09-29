-- Prove2me | Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
-- name    : ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/8d276aae-c3cd-522f-bb94-739347d907b4
-- title:
--   Attachment of the wide supersingular annulus to a component chart
-- statement:
--   Fix a prime $p\ge 5$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k$ is algebraically closed of characteristic $p$, and let $\overline{F}_i$ be a field extension of $k$. Let $C_i$ be a `ComponentChart` for $A$ on the field $F=$ `modularFunctionFieldBar (1 * p)` with residue target $\overline{F}_i$, and $x_i$ a place of $\overline{F}_i$ over $k$ lying in $C_i.\mathrm{nodes}$. Let $a\in k$ satisfy: every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point (membership in `ssJSet p k`), $a^{p^2}=a$, and $a=0$ or $a=1728$. Let $\mathrm{An}'$ be an `Annulus` for $A$ on $F$ with parameter $z'$, with $z'z$ equal to the image of $\mathrm{An}'.\mathrm{modulus}$ for some $z\in F$, with $\mathrm{An}'.\mathrm{modulus}=p^{\,\mathrm{jWidth}\,a}$ (so the exponent is $3$ for $a=0$ and $2$ for $a=1728$), and whose set of places is exactly those $W$ for which both $j$ minus some lift of $a$ and $j(q^p)$ minus some lift of $a^p$ have strictly positive $W$-order. Assume further: $z'$ and $\mathrm{frickeInvolutionBar}\,(1\cdot p)\,z$ lie in the localized modular ring, have nonzero reductions under `modularRedLocHom` lying in `modularFunctionFieldC k 1`, and those reductions have order $1$ at the places `charLGeomPlaceOfPoint k a`, respectively `charLGeomPlaceOfPoint k (a ^ p)`; every element of $F$ lying in the localized modular ring with nonzero reduction lies in $C_i.\mathrm{integers}$ with nonzero $C_i$-residue; and for every $g\in C_i.\mathrm{integers}$ in the localized modular ring with reduction in `modularFunctionFieldC k 1`, the $x_i$-order of $C_i.\mathrm{residue}\,g$ equals the order of that reduction at `charLGeomPlaceOfPoint k a`. The conclusion is $\mathrm{An}'.\mathrm{IsAttached}\ C_i\ x_i$: namely $x_i$ is a node of $C_i$, the parameter $\mathrm{An}'.\mathrm{param}$ lies in $C_i.\mathrm{integers}$ and its residue has $x_i$-order $1$, and for every $f\in C_i.\mathrm{integers}$ with nonzero residue and order $0$ at all places of $\mathrm{An}'.\mathrm{dom}$, and every such place $P$, the element $P.\mathrm{evalAt}\,f\cdot (P.\mathrm{evalAt}\,\mathrm{An}'.\mathrm{param})^{-x_i.\mathrm{ord}(C_i.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there.
--
--   This records the local geometry of $X_0(p)$ over a valuation ring above $p$ at a supersingular crossing with $j$-invariant $0$ or $1728$: the annulus surrounding the crossing, taken with the end opposite to the one normalised by the $j$-coordinate, is attached at the node to the component chart through the cusp $\infty$, the width of the node being $3$ or $2$ according to the extra automorphisms. It feeds the assembly of charts and annuli into a semistable model in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel), its variant for $a\in\{0,1728\}$, and [`ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne`](thm.html#ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.lean

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

theorem ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type}
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
