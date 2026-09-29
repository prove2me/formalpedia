-- Prove2me | Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
-- name    : ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7fabc00c-6c36-50e8-b2c2-880239cc5eb8
-- title:
--   Deuring's inequality for reduced q-expansion function fields
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $A \subseteq L$ be a valuation subring, write $k =$ `IsLocalRing.ResidueField A` for its residue field, and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index with $T = \begin{pmatrix}1&1\\0&1\end{pmatrix} \in \Gamma$. For a field $K$, [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) denotes the intermediate field of $K((q))$ generated over $K$ by the ratios $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of one and the same weight on $\Gamma$ (viewed inside $\mathrm{GL}_2(\mathbb{R})$) with integral $q$-expansions $p_f,p_g$ in the sense of `IsIntegralQExp`, and $\mathrm{intSeriesC}\,K\,p_g \ne 0$; and [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) is the Laurent series $q^{-1}$ times the image in $K$ of $\mathrm{jNum} = E_4^3 \cdot \mathrm{dedekindEtaUnitInv} \in \mathbb{Z}[[q]]$. The assertion is that there is an element $x$ of [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) whose underlying Laurent series is [`ModularCurve.jqModC k`](def/ModularCurve_JqCoeff.html#L15), such that $x$ is transcendental over $k$, such that [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) is finite-dimensional over the subfield $k(x)$, and such that for every element $y$ of [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103) — the subfield of $L((q))$ generated over $L$ by the coefficientwise image of [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) — whose underlying Laurent series is [`ModularCurve.jqModC L`](def/ModularCurve_JqCoeff.html#L15), one has $[\,$`qExpFunctionFieldC k Γ`$: k(x)] \le [\,$`laurentBaseChange L (qExpFunctionFieldC ℚ Γ)`$: L(y)]$.
--
--   This is Deuring's inequality for the reduction of the $q$-expansion function field of $X(\Gamma)$ at an arbitrary place of the field of constants: the reduced field is again an algebraic function field of one variable over the residue field, finite over $k(\bar\jmath)$ of degree at most the generic degree, with no restriction on the residue characteristic relative to the level. It supplies the one-variable function field structure on the special fibre used throughout the specialisation and prolongation arguments that produce models of the modular curves and of their Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ,
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
      Transcendental (IsLocalRing.ResidueField A) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ∧
      ∀ (y : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        (y : LaurentSeries L) = ModularCurve.jqModC L →
        Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
            (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ≤
          Module.finrank
            (IntermediateField.adjoin L
              ({y} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
            (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by sorry
