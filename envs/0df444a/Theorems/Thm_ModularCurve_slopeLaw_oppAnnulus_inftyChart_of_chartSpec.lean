-- Prove2me | Theorems.Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec
-- name    : ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e4e7c3af-af07-520c-8324-3c0fa216fa84
-- title:
--   Slope law for the opposite supersingular annulus
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k$ has characteristic $p$ and is algebraically closed, and let $F = \mathtt{modularFunctionFieldBar}\ p$ be the base change to $\overline{\mathbb Q}$ of the full modular function field of level $p$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$. Let $F_i$ be a field extension of $k$, let $C_i$ be a `ComponentChart` for $A$, $F$ and $F_i$ (a valuation subring $C_i.\mathrm{integers}$ of $F$, a surjective residue map to $F_i$ with kernel the maximal ideal, a domain of places, a finite set of nodes, a place map, and the compatibility axioms of that structure), and let $x_i$ be a place of $F_i$ over $k$. Let $a \in k$ satisfy $a^{p^2} = a$, $a \ne 0$, $a \ne 1728$ and $a \in \mathtt{ssJSet}\ p\ k$, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point. Write $j$ and $j_p$ for the elements of $F$ given by the $q$-expansion $\mathtt{jq}$ and by its $p$-fold dilation $\mathtt{qExpand}\ \mathbb{Q}\ p\ \mathtt{jq}$, both transported by $\mathtt{coeffEmb}$. Let $An'$ be an `Annulus` for $A$ and $F$ such that (i) its parameter satisfies $An'.\mathrm{param} \cdot (j_p - j^{\,p}) = p$ in $F$, and (ii) a place $W$ of $F$ over $\overline{\mathbb Q}$ lies in $An'.\mathrm{dom}$ exactly when there are $x, y \in A$ with residues $a$ and $a^p$ such that $W.\mathrm{ord}(j - x) > 0$ and $W.\mathrm{ord}(j_p - y) > 0$. Assume two compatibilities between the chart and reduction modulo the maximal ideal of $A$: first, every $g \in F$ whose Laurent series lies in $\mathtt{CharPReduction.modularLocalized}\ p\ A\ (\text{residue})$ and has nonzero image under $\mathtt{modularRedLocHom}$ belongs to $C_i.\mathrm{integers}$ with nonzero chart residue; second, for every $g \in C_i.\mathrm{integers}$ whose Laurent series lies in that localized ring and whose reduction lies in $\mathtt{modularFunctionFieldC}\ k\ 1$, the order of $C_i.\mathrm{residue}\ g$ at $x_i$ equals the order of that reduction at the place $\mathtt{charLGeomPlaceOfPoint}\ k\ a$. The conclusion is that for every $f \in C_i.\mathrm{integers}$ with $C_i.\mathrm{residue}\ f \ne 0$ and $P.\mathrm{ord}\ f = 0$ for all $P \in An'.\mathrm{dom}$, and for every $P \in An'.\mathrm{dom}$, the value $P.\mathrm{evalAt}\ f \cdot (P.\mathrm{evalAt}\ An'.\mathrm{param})^{-\mathrm{ord}_{x_i}(C_i.\mathrm{residue}\ f)}$ lies in $A$ and is a unit of $A$.
--
--   This is the slope law along the supersingular annulus with parameter $p/(j_p - j^{\,p})$ on the chart through $\infty$ of the Deligne–Rapoport model of $X_0(p)$ over $A$: the radial slope of a chart unit along the annulus is its order of vanishing at the node $x_i$. It is one of the three clauses of the attachment of this annulus to that component, and is used by [`ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec`](thm.html#ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec) and by its level-one form [`ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne`](thm.html#ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharPReduction
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

theorem ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar p) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar p))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (p : AlgebraicClosure ℚ))
    (hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An'.dom ↔
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
    (hunit : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 → ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar p)) (hf : f ∈ Ci.integers), Ci.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom,
        ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(xi.ord (Ci.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by sorry
