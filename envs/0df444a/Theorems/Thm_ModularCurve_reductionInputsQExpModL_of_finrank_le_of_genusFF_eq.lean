-- Prove2me | Theorems.Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
-- name    : ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/2b149787-d9bd-566b-932f-6f7907990fcb
-- title:
--   Deuring reduction data for q-expansion modular curves
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`, with residue field $k=$ `IsLocalRing.ResidueField A`. For a field $K$, [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) is the intermediate field of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of a common weight on $\Gamma$ with integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ and the image of $p_g$ in $K((q))$ is nonzero; [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) is the subfield of $L((q))$ generated over $L$ by the coefficientwise image of $F₀\subseteq\mathbb{Q}((q))$; and [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) is the Laurent series $q^{-1}$ times the image in $K[[q]]$ of [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142) $=E_4^3\cdot$`dedekindEtaUnitInv`, i.e. the $q$-expansion of $j$ over $K$. Two hypotheses are assumed: (degree) whenever $x$ in `qExpFunctionFieldC k Γ` and $y$ in `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` have underlying Laurent series `jqModC k` and `jqModC (AlgebraicClosure ℚ)` respectively, the degree of `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` over $\overline{\mathbb{Q}}(y)$ is at most the degree of `qExpFunctionFieldC k Γ` over $k(x)$; and (genus) [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145), defined as the dimension over the constant field of $H^1$ of the zero divisor, takes the same value for `qExpFunctionFieldC k Γ` over $k$ as for `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` over $\overline{\mathbb{Q}}$. The conclusion is [`ModularCurve.ReductionInputsQExpModL A Γ`](def/ModularCurve_QExpReductionModL.html#L296): there is a map $r$ from the places of `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` over $\overline{\mathbb{Q}}$ to the places of `qExpFunctionFieldC k Γ` over $k$ satisfying the predicate `IsLaurentPlaceReduction` for $A$ with its residue map, together with the predicate `LaurentPrincipalGeneratedByIntegral` for the same data.
--
--   This is Deuring's criterion for good reduction of a one-variable function field with respect to a place of the field of constants, specialised to a modular curve presented by $q$-expansions, where the reduction is read off coefficientwise: equality of the degree over the $j$-line and of the genus forces the reduction of places to be well behaved. It supplies the reduction data used by [`ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd`](thm.html#ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd), the good-reduction input for the curves $X_H$ at primes not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hdeg : ∀ (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)
      (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) →
      (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ))
    (hgen : AlgebraicCurve.genusFF (IsLocalRing.ResidueField A)
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    ModularCurve.ReductionInputsQExpModL A Γ := by sorry
