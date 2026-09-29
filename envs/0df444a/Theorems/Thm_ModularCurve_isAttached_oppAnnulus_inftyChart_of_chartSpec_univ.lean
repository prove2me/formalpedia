-- Prove2me | Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_univ
-- name    : ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c3d1c019-1abc-54da-a7bc-3fa4955dc4bf
-- title:
--   Attachment of the opposite supersingular annulus to the ∞-chart
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$ and is algebraically closed; let $F = \overline{\mathbb Q}\cdot\mathrm{modularFunctionFieldFull}\,p$ be the indicated intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ denoted `modularFunctionFieldBar p`, and write $j$ and $j_p$ for the elements of $F$ given by the coefficient images of the $q$-expansion `jq` and of its substitution $q \mapsto q^{p}$. Let $F_i$ be a field over $k$, let $C_i$ be a component chart of $F$ along $A$ with values in $F_i$ (a valuation subring $C_i.\mathrm{integers}$ of $F$, a surjective residue map onto $F_i$ with kernel the maximal ideal, a set of places of $F$ over $\overline{\mathbb Q}$, a finite set of node places of $F_i$ over $k$, and a place map, subject to the chart axioms), and let $X_i \in F_i$ and $x_i \colon k \to \mathrm{Place}(k, F_i)$ be such that for every $c \in k$ and every $P \in k[T]$ one has $\mathrm{ord}_{x_i(c)}(P(X_i)) = \mathrm{mult}_c(P)$. Assume $j$ and $j_p$ lie in $C_i.\mathrm{integers}$ with residues $X_i$ and $X_i^{p}$, and that $x_i(b)$ is a node of $C_i$ for every $b$ in $\mathrm{ssJSet}\,p\,k$, the set of $j$-invariants $b$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $b$ has no nonzero $p$-torsion point. Fix $a \in \mathrm{ssJSet}\,p\,k$ with $a^{p^{2}} = a$, $a \ne 0$ and $a \ne 1728$. Let $\mathrm{An}'$ be an annulus along $A$ in $F$ (a set of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the annulus axioms) whose parameter $z'$ satisfies $z' \cdot (j_p - j^{p}) = p$, and whose domain consists exactly of the places $W$ of $F$ for which both $j$ and $j_p$ are congruent to elements of $A$ reducing to $a$ and to $a^{p}$ respectively, in the sense that $\mathrm{ord}_W(j - x) > 0$ for some $x \in A$ with residue $a$ and $\mathrm{ord}_W(j_p - y) > 0$ for some $y \in A$ with residue $a^{p}$. Assume further: every $g \in F$ lying in the localised modular ring $\mathrm{modularLocalized}\,p$ for $A$ and the residue map of $A$ whose image under $\mathrm{modularRedLocHom}$ is nonzero lies in $C_i.\mathrm{integers}$ with nonzero residue; and for every such $g$ in $C_i.\mathrm{integers}$ whose image under $\mathrm{modularRedLocHom}$ lies in $\mathrm{modularFunctionFieldC}\,k\,1$, the order of $C_i$-residue of $g$ at $x_i(a)$ equals the order of that image at the place $\mathrm{charLGeomPlaceOfPoint}\,k\,a$. Then $\mathrm{An}'$ is attached to $C_i$ at $x_i(a)$: the place $x_i(a)$ is a node of $C_i$, the parameter $z'$ lies in $C_i.\mathrm{integers}$ and its residue has order exactly $1$ at $x_i(a)$, and for every $f \in C_i.\mathrm{integers}$ with nonzero residue and $\mathrm{ord}_P f = 0$ at all $P$ in the domain of $\mathrm{An}'$, and every such $P$, the element $f(P)\cdot z'(P)^{-\mathrm{ord}_{x_i(a)}(\overline f)}$ lies in $A$ and is a unit there.
--
--   This is the gluing step for the semistable covering of $X_0(p)$ in function-field form: the supersingular annulus presented with the parameter $z' = p/(j_p - j^{p})$ is attached to the component of the special fibre through the cusp $\infty$ at the node with coordinate $X = a$. It is used in the level-one specialisation [`ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ`](thm.html#ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ), en route to the uniform multiplicative covering structure for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_univ.lean

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

theorem ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_univ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)] (hp5 : 5 ≤ p)
    {Fbari : Type*} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar p) Fbari)
    (Xi : Fbari) (xpli : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbari)
    (hord_polyi : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpli c).ord (Polynomial.aeval Xi P) = (P.rootMultiplicity c : ℤ))
    (hjFi : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ∈ Ci.integers)
    (hjpFi : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p) ∈ Ci.integers)
    (hres_ji : Ci.residue ⟨_, hjFi⟩ = Xi) (hres_jpi : Ci.residue ⟨_, hjpFi⟩ = Xi ^ p)
    (hnodesi : ∀ b ∈ ssJSet p (IsLocalRing.ResidueField ↥A), xpli b ∈ Ci.nodes)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar p))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p) - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
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
        (xpli a).ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An'.IsAttached Ci (xpli a) := by sorry
