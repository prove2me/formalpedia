-- Prove2me | Theorems.Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne
-- name    : ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/153706e0-0f7c-5799-82d6-99625b9bd3a7
-- title:
--   Slope law of the opposite supersingular annulus, level 1· p
-- statement:
--   Fix a prime $p$ with $5 \le p$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k$ is algebraically closed of characteristic $p$, and a field $\bar F_i$ that is a $k$-algebra. Write $F =$ `modularFunctionFieldBar (1 * p)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot p$ inside $\overline{\mathbb{Q}}((q))$, and let $j, j_{1\cdot p} \in F$ be the elements coming from the $q$-expansion `jq` and from its image under `qExpand ℚ (1 * p)`. Given a component chart $C_i$ of $F$ along $A$ with residue target $\bar F_i$, a place $x_i$ of $\bar F_i$ over $k$, and $a \in k$ with $a \ne 0$, $a \ne 1728$, $a^{p^2} = a$ and $a \in$ `ssJSet p k` (every elliptic Weierstrass curve over $k$ of $j$-invariant $a$ has only the zero point killed by $p$), suppose an annulus $An'$ of $F$ along $A$ satisfies: its parameter $z'$ obeys $z' \cdot (j_{1\cdot p} - j^{\,p}) = p$; a place $W$ of $F$ over $\overline{\mathbb{Q}}$ lies in $An'.\mathrm{dom}$ exactly when there are $x, y \in A$ with residues $a$ and $a^{p}$ such that $W.\mathrm{ord}(j - x) > 0$ and $W.\mathrm{ord}(j_{1\cdot p} - y) > 0$; every $g \in F$ whose Laurent series lies in `CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue A)` and has nonzero image under `CharPReduction.modularRedLocHom` is a $C_i$-integer with nonzero chart residue; and for every $C_i$-integer $g$ whose Laurent series lies in that localisation and whose reduction lies in `modularFunctionFieldC k 1`, the order at $x_i$ of its chart residue equals the order of that reduction at `charLGeomPlaceOfPoint k a`. Then for every $f \in C_i$`.integers` with nonzero chart residue and with $P.\mathrm{ord}\, f = 0$ at all $P \in An'.\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}\,f \cdot (P.\mathrm{evalAt}\,z')^{-\,x_i.\mathrm{ord}(C_i\text{-residue of } f)}$ of $\overline{\mathbb{Q}}$ lies in $A$ and is a unit there.
--
--   This is the slope law for the annulus with parameter $p/(j_{1\cdot p}-j^{\,p})$ at a width-one supersingular node of the Deligne–Rapoport model of $X_0(p)$ in characteristic $p$: along the annulus, the slope of a chart unit is its order at the node. It is one of the clauses of the attachment of such an annulus to the component through infinity, and is used in the construction of component charts and annuli attached to a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne.lean

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

theorem ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne
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
    (h0 : a ≠ 0)
    (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
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
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (hf : f ∈ Ci.integers), Ci.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom,
        ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(xi.ord (Ci.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by sorry
