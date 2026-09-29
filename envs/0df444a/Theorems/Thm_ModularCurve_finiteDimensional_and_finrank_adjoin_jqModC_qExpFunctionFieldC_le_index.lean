-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
-- name    : ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/da6f3bde-beb3-5d0b-b5b9-58f863f595fa
-- title:
--   Degree of the q-expansion function field over the j-line
-- statement:
--   Let $K$ be a field, let $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$ be a subgroup of finite index containing the translation matrix `ModularGroup.T`, and let $\Gamma' \le \mathrm{SL}(2,\mathbb{Z})$ be a subgroup with $\Gamma \le \Gamma'$ such that every $\gamma \in \Gamma'$ satisfies $\gamma \in \Gamma$ or $-\gamma \in \Gamma$ (so $\Gamma'$ lies between $\Gamma$ and $\pm\Gamma$). Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the set `intFormRatiosC K Γ`, namely by all quotients `intSeriesC K pf / intSeriesC K pg` where $k \in \mathbb{Z}$, $f$ and $g$ are modular forms of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$, and $p_f, p_g$ are power series over $\mathbb{Z}$ satisfying the predicate `IsIntegralQExp` for $f$ and for $g$ respectively, with `intSeriesC K pg ≠ 0`. Let $x \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the image over $K$ of the integral power series `jNum` $=$ `eisenstein4 ^ 3 * dedekindEtaUnitInv`. Then $F$ is finite-dimensional over the subfield $K(x)$ obtained by adjoining $x$ to $K$, and $[F : K(x)] \le [\mathrm{SL}(2,\mathbb{Z}) : \Gamma']$.
--
--   This is the field-independent form of the classical upper bound for the degree of the modular curve $X(\Gamma)$ over the $j$-line, with the bound given by the index of a subgroup between $\Gamma$ and $\pm\Gamma$ rather than of $\Gamma$ itself. It underlies the computations of degrees and of function fields of modular curves over arbitrary base fields used later in the formalisation, and is cited by the index computations for $\Gamma_0(N)$ and by the study of the Igusa models at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by sorry
