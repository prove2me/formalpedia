-- Prove2me | Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
-- name    : ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/a11d76ff-6c71-561d-af4e-2c6d92065c93
-- title:
--   Constant reduction realising the q-expansion reduction on Pic⁰
-- statement:
--   Let $\Gamma\le \mathrm{SL}(2,\mathbb Z)$ be a subgroup of finite index containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $A$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ`, with residue field $k=$ `IsLocalRing.ResidueField A`. Write $F(\Gamma)=$ `qExpFunctionFieldC ℚ Γ` for the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by `intFormRatiosC ℚ Γ`, and likewise $\bar F(\Gamma)=$ `qExpFunctionFieldC k Γ` inside $k((q))$; let $F=$ `laurentBaseChange` be the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of $F(\Gamma)$. Assume `ReductionInputsQExpModL A Γ`, i.e. that there is a map $r$ from the places of $F/\overline{\mathbb Q}$ to those of $\bar F(\Gamma)/k$ satisfying `IsLaurentPlaceReduction` for $A$, the residue map of $A$ and these two fields, together with `LaurentPrincipalGeneratedByIntegral`. Then there exists a `ConstantReduction` of $A$ relative to $F$ and $\bar F(\Gamma)$ — a valuation subring $\mathcal O\subseteq F$ whose intersection with $\overline{\mathbb Q}$ is $A$, together with a surjective residue homomorphism $\mathcal O\to\bar F(\Gamma)$ with kernel the maximal ideal of $\mathcal O$, extending the residue map of $A$, such that every nonzero element of $F$ has a nonzero residue after scaling by a constant, and with a degree-preserving map on places compatible with divisors of elements of $\mathcal O$ of nonzero residue — whose place map is the chosen $r$, namely `placeReductionQExpModL h`, whose induced map on degree-zero divisor classes is `reductionQExpModL A Γ`, and which is given on $q$-expansions by coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((q))$ lies in $F$ and whose coefficientwise reduction lies in $\bar F(\Gamma)$, that image lies in $\mathcal O$ and its residue is the coefficientwise reduction of $y$.
--
--   This identifies the reduction map on $\mathrm{Pic}^0$ of the modular function field of level $\Gamma$, defined through a reduction of places in Deuring's sense, with the map on divisor classes coming from an honest constant reduction, the Gauss prolongation of $A$ read off from $q$-expansions. It is the bridge through which the general theory of constant reductions is applied to the Jacobian of $X(\Gamma)$, and is used for the levels $\Gamma_H(M)$, $\Gamma_1(M)$ and $\Gamma_0(M)$ in statements on torsion and on the action of diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsQExpModL A Γ) :
    ∃ R : ConstantReduction A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      R.placeMap = ModularCurve.placeReductionQExpModL h ∧
      R.pic0Map = ModularCurve.reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
              ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ := by sorry
