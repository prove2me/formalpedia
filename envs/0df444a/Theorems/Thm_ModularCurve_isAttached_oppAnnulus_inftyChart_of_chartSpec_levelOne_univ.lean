-- Prove2me | Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ
-- name    : ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/f2dacd06-f85c-5c1c-9d74-3db1c0c0adc1
-- title:
--   Attachment of the opposite supersingular annulus, level 1· p
-- statement:
--   Fix a prime $p\ge 5$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $p$, is algebraically closed and has decidable equality, together with a field $Fbari$ over $\kappa$. Let $Ci$ be a component chart for $A$ on the field $modularFunctionFieldBar (1*p)$ (the base change to $\overline{\mathbb Q}$ of the full level-$1\cdot p$ modular function field inside Laurent series) with values in $Fbari$, let $Xi \in Fbari$, and let $xpli$ assign to each $c \in \kappa$ a place of $Fbari$ over $\kappa$, in such a way that for every $c$ and every polynomial $P$ over $\kappa$ the order of $P(Xi)$ at $xpli\,c$ is the multiplicity of $c$ as a root of $P$. Assume the elements $j$ (the coefficient image of `jq`) and $j_p$ (the coefficient image of `qExpand ℚ (1*p) jq`) lie in the valuation subring `Ci.integers`, with residues $Xi$ and $Xi^p$ respectively, and that $xpli\,b$ is a node of $Ci$ for every $b$ in $ssJSet\,p\,\kappa$, i.e. every $b$ such that every elliptic curve over $\kappa$ with $j$-invariant $b$ has no nonzero $p$-torsion point. Let $a \in ssJSet\,p\,\kappa$ satisfy $a^{p^2}=a$, $a \neq 0$ and $a \neq 1728$. Let $An'$ be an annulus for $A$ on the same field whose parameter $z'$ satisfies $z'\,(j_p - j^p) = p$ and whose domain consists exactly of those places $W$ for which $j$ is congruent to $a$ and $j_p$ is congruent to $a^p$, in the sense that there are $x,y \in A$ with residues $a$ and $a^p$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j_p-y)>0$. Assume further two compatibilities between the chart and the reduction of Laurent coefficients: every $g$ whose Laurent series lies in $modularLocalized (1*p)$ for $A$ and the residue map, and whose image under $modularRedLocHom$ is nonzero, lies in `Ci.integers` with nonzero residue; and for such $g$ in `Ci.integers` whose reduction lies in $modularFunctionFieldC\,\kappa\,1$, the order of $Ci.residue\,g$ at $xpli\,a$ equals the order of that reduction at $charLGeomPlaceOfPoint\,\kappa\,a$. The conclusion is that $An'$ is attached to $Ci$ at $xpli\,a$: the place $xpli\,a$ is a node of $Ci$, the parameter $z'$ lies in `Ci.integers` and its residue has order $1$ at $xpli\,a$, and for every $f \in Ci.integers$ with nonzero residue and order $0$ at all places of $An'.dom$, and every such place $P$, the value $P(f)\cdot P(z')^{-\mathrm{ord}_{xpli\,a}(Ci.residue\,f)}$ lies in $A$ and is a unit there.
--
--   In the semistable model of $X_0(p)$ over a place of $\overline{\mathbb Q}$ above $p$, the supersingular points are joined to the two rational components by annuli; this statement identifies the annulus cut out by $z'(j_p-j^p)=p$ around the supersingular value $a$ as the one attached, at the node $xpli\,a$, to the chart of the component on which $j_p = j^p$. It is the restatement at level $1\cdot p$ of [`ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ`](thm.html#ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ), and is used in the construction of component charts and annuli for prolongation tuples over a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ.lean

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

theorem ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ
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
    (Xi : Fbari)
    (xpli : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbari)
    (hord_polyi : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpli c).ord (Polynomial.aeval Xi P) = (P.rootMultiplicity c : ℤ))
    (hjFi : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ∈ Ci.integers)
    (hjpFi : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p)) ∈ Ci.integers)
    (hres_ji : Ci.residue ⟨_, hjFi⟩ = Xi)
    (hres_jpi : Ci.residue ⟨_, hjpFi⟩ = Xi ^ p)
    (hnodesi : ∀ b ∈ ssJSet p (IsLocalRing.ResidueField ↥A), xpli b ∈ Ci.nodes)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0)
    (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p)) - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ))
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
    (hunit : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 → ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        (xpli a).ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An'.IsAttached Ci (xpli a) := by sorry
