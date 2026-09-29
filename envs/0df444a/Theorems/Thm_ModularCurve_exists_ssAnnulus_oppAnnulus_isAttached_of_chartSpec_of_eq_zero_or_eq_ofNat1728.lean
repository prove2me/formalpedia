-- Prove2me | Theorems.Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728
-- name    : ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/dae29ebc-fe14-5858-ad19-7e655b35fefc
-- title:
--   Wide supersingular annuli of X₀(p) attached to both charts
-- statement:
--   Let $p\ge 5$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k$ is algebraically closed of characteristic $p$; put $F=\mathtt{modularFunctionFieldBar}\ p$, the base change to $\overline{\mathbb Q}$ of the full level-$p$ modular function field inside Laurent series. Given two component charts $C_0$, $C_i$ of $F$ along $A$ with values in field extensions $\bar F_0$, $\bar F_i$ of $k$ (each a valuation subring of $F$ together with a surjective residue map onto the chart field with kernel the maximal ideal, a set of places of $F$ over $\overline{\mathbb Q}$, a finite set of node places over $k$ and the compatibility axioms of `ComponentChart`), node places $x_0\in C_0.\mathtt{nodes}$ and $x_i\in C_i.\mathtt{nodes}$, and $a\in k$ lying in $\mathtt{ssJSet}\ p\ k$ (every elliptic curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point) with $a^{p^2}=a$ and $a=0$ or $a=1728$. Assume two dictionaries between the Gauss reduction and the charts: (i) for $g\in F$ whose Fricke involute lies in $\mathtt{modularLocalized}\ p$ with nonzero image under $\mathtt{modularRedLocHom}$, $g$ lies in $C_0.\mathtt{integers}$ with nonzero residue, and whenever moreover that image lies in the level-one field $\mathtt{modularFunctionFieldC}\ k\ 1$, the order at $x_0$ of the $C_0$-residue of $g$ equals the order of the image at the place $\mathtt{charLGeomPlaceOfPoint}\ k\ (a^p)$; (ii) the same statements for $g$ itself (without the Fricke involution), for $C_i$, $x_i$ and the place at $a$. Then there are annuli $\mathrm{An},\mathrm{An}'$ of $F$ along $A$ with the same domain and the same modulus $m$, with $m\ne 0$ in $\overline{\mathbb Q}$ and $\mathrm{An}'.\mathtt{param}\cdot \mathrm{An}.\mathtt{param}=m$ in $F$, such that $\mathrm{An}$ is attached to $(C_0,x_0)$ and $\mathrm{An}'$ to $(C_i,x_i)$ in the sense of `IsAttached` (the parameter lies in the chart's integers, its residue has order $1$ at the node, and chart units are, after dividing by the appropriate power of the parameter, units at every place of the annulus), the common domain consists exactly of those places $W$ of $F$ over $\overline{\mathbb Q}$ for which $W.\mathtt{ord}(j_q-x)>0$ for some $x\in A$ with residue $a$ and $W.\mathtt{ord}(j_q(q^p)-y)>0$ for some $y\in A$ with residue $a^p$, and $\mathrm{An}.\mathtt{modulus}=p^{\mathtt{jWidth}\ a}$ in $A$, where $\mathtt{jWidth}\ a$ is $3$ for $a=0$ and $2$ for $a=1728$.
--
--   This is the supersingular edge of the semistable covering of $X_0(p)$ at a node with extra automorphisms, where the local equation is $xy=p^{e}$ with $e=3$ for $j=0$ and $e=2$ for $j=1728$; the annulus pair records the two branches through the node together with their attachments to the charts of the two irreducible components. It is used by the statements producing component charts and annuli for a prolongation tuple over a model, alongside the width-one companion for the remaining supersingular $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728.lean

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

theorem ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728 (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type} [Field Fbar0] [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar p) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    {Fbari : Type} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar p) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodes0 : x0 ∈ C0.nodes) (hnodesi : xi ∈ Ci.nodes)
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))
    (huniti : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar p)),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      An.IsAttached C0 x0 ∧ An'.IsAttached Ci xi ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (y : AlgebraicClosure ℚ))))) ∧
      An.modulus = ((p : ℕ) : ↥A) ^ jWidth a := by sorry
