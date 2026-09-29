-- Prove2me | Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
-- name    : ModularCurve.isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/557e5a7e-94a2-5680-a336-d00436948d57
-- title:
--   The q-expansion field over a residue field is a curve
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $A \subseteq L$ be a valuation subring whose residue field $k =$ `IsLocalRing.ResidueField A` is perfect, and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix `ModularGroup.T`. Write $F =$ [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $k((q))$ generated over $k$ by the set of quotients $\mathrm{intSeriesC}_k(p_f)/\mathrm{intSeriesC}_k(p_g)$, taken over all weights $k'$, all modular forms $f, g$ of weight $k'$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, and all power series $p_f, p_g$ over $\mathbb{Z}$ that are integral $q$-expansions of $f$ and of $g$ respectively, with $\mathrm{intSeriesC}_k(p_g) \neq 0$. The conclusion is twofold. First, $F$ is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ of $F/k$ (a valuation subring of $F$ containing $k$, distinct from $F$, and a principal ideal ring) and $\deg D = 0$; every place has residue field finite over $k$; and $\Omega_{F/k}$ is free of rank $1$ over $F$. Second, there is a finite subset $s \subseteq F$ with $k(s) = F$.
--
--   This is the statement that the $q$-expansion function field of $X(\Gamma)$, formed over the residue field of a valuation subring of a characteristic-zero field, is a one-variable function field over that residue field and is finitely generated. It supplies the curve-structure and finite-generation hypotheses used downstream in the specialisation and reduction arguments for places of the $j$-line, including the analysis of prolongation data and of section pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L) [PerfectField (IsLocalRing.ResidueField ↥A)]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ) ∧
      ∃ s : Finset ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ),
        IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
          (s : Set ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ)) = ⊤ := by sorry
