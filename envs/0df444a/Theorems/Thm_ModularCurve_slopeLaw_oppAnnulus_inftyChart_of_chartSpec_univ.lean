-- Prove2me | Theorems.Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec_univ
-- name    : ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e8c2301e-ef05-510a-941c-84ee184545d1
-- title:
--   Slope law on the infinity chart for the opposite annulus
-- statement:
--   Fix a prime $p \ge 5$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k$ is algebraically closed of characteristic $p$, and let $F = \overline{\mathbb{Q}}\cdot\,$`modularFunctionFieldFull p`, the base change to $\overline{\mathbb{Q}}$ of the full level-$p$ modular function field inside Laurent series. Let $j, j_p \in F$ denote the classes of the $q$-expansions `jq` and `qExpand ℚ p jq`. Given a field $F_i$ over $k$, let $C_i$ be a component chart of $F$ along $A$ with values in $F_i$ (a valuation subring `integers` of $F$ contracting to $A$, a surjective residue map to $F_i$ with kernel the maximal ideal, a set of places, a finite set of nodes and a place map, subject to the pointwise and divisor-pushforward axioms), and let $x_i$ be a place of $F_i$ over $k$. Let $a \in k$ satisfy $a^{p^2}=a$, $a \neq 0$, $a \neq 1728$ and $a \in$ `ssJSet p k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point. Let $An'$ be an annulus of $F$ along $A$ whose parameter $z'$ satisfies $z' \cdot (j_p - j^{p}) = p$ and whose domain consists exactly of the places $W$ of $F$ over $\overline{\mathbb{Q}}$ for which there are $x, y \in A$ with residues $a$ and $a^{p}$ respectively and $\operatorname{ord}_W(j - x) > 0$, $\operatorname{ord}_W(j_p - y) > 0$. Assume two compatibilities between $C_i$ and the characteristic-$p$ reduction of Laurent series at $A$: first, every $g \in F$ whose Laurent series lies in `CharPReduction.modularLocalized p A.toSubring` and has nonzero image under `CharPReduction.modularRedLocHom` belongs to $C_i$.`integers` with nonzero chart residue; second, for every such $g$ lying in $C_i$.`integers` whose reduction moreover lies in `modularFunctionFieldC k 1`, the order at $x_i$ of its chart residue equals the order of that reduction at the place `charLGeomPlaceOfPoint k a`. The conclusion is that for every $f \in C_i$.`integers` with nonzero chart residue $\bar f$ and with $\operatorname{ord}_P f = 0$ at all $P \in An'$.`dom`, and for every such $P$, the value $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}(z'))^{-\operatorname{ord}_{x_i}\bar f}$ lies in $A$ and is a unit there.
--
--   This is the slope law for the supersingular annulus with parameter $p/(j_p - j^{p})$ on the chart of the Deligne–Rapoport model of $X_0(p)$ through the cusp $\infty$ in characteristic $p$: along the annulus, the slope of a chart unit is its order of vanishing at the node. It supplies one of the three clauses of the attachment of this annulus to the component through infinity, and is used by [`ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ`](thm.html#ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec_univ.lean

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

theorem ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_univ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type*} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
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
