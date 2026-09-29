-- Prove2me | Theorems.Thm_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ
-- name    : ModularCurve.slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/9ff30a5b-c512-5fec-9d07-64e831b0b1d3
-- title:
--   Slope law on the supersingular annulus at the 0-chart
-- statement:
--   Fix a prime $p\ge 5$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k=\kappa(A)$ has characteristic $p$ and is algebraically closed. Let $Fbar_0$ be a field extension of $k$, let $C_0$ be a component chart for the field $F=\overline{\mathbb{Q}}\cdot\mathbb{Q}(X(p)^{\mathrm{full}})$ (`modularFunctionFieldBar p`) relative to $A$ with residue target $Fbar_0$ — that is, a valuation subring `C0.integers` of $F$ with surjective residue map onto $Fbar_0$ having kernel the maximal ideal, a domain of places, a finite node set, a place map and the compatibility axioms of `ComponentChart` — and let $x_0$ be a place of $Fbar_0$ over $k$. Let $a\in k$ satisfy: every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has trivial $p$-torsion, $a^{p^2}=a$, $a\neq 0$ and $a\neq 1728$. Let $\mathrm{An}$ be an annulus for $A$ in $F$ whose parameter is $G=j(q^p)-j(q)^p$ (the images under `coeffEmb` of `qExpand ℚ p jq` and of `jq`), and whose domain consists exactly of those places $W$ for which there are $x,y\in A$ with residues $a$ and $a^p$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j(q^p)-y)>0$. Assume two compatibilities between $C_0$ and the reduction apparatus along the other component: first, whenever the Laurent series of $w_p(g)$ lies in `CharPReduction.modularLocalized p A.toSubring (residue A)` and has nonzero image under `modularRedLocHom`, then $g$ lies in `C0.integers` with nonzero residue; second, for $g\in$ `C0.integers` such that this image moreover lies in `modularFunctionFieldC k 1`, the order of $C_0$'s residue of $g$ at $x_0$ equals the order of that image at the place `charLGeomPlaceOfPoint k (a ^ p)`. The conclusion: for every $f\in$ `C0.integers` with nonzero residue and with $P.\mathrm{ord}\,f=0$ at all places $P$ of the annulus, and every such $P$, the value $P(f)\cdot P(G)^{-\operatorname{ord}_{x_0}(\bar f)}$ lies in $A$ and is a unit there.
--
--   This is the slope law for the supersingular annulus with parameter $G=j(q^p)-j(q)^p$, read at the end lying on the component of $X_0(p)\otimes\mathbb{F}_p$ through the cusp $0$: a chart unit without zeros or poles on the annulus has slope along the annulus equal to the order of its reduction at the node. It supplies the third clause of the attachment of this annulus to the $0$-chart and is used by [`ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ`](thm.html#ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.lean

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

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type*} [Field Fbar0] [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar p) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An : Annulus A ↥(modularFunctionFieldBar p))
    (hparam : An.param = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An.dom ↔
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
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar p)) (hf : f ∈ C0.integers), C0.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x0.ord (C0.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by sorry
