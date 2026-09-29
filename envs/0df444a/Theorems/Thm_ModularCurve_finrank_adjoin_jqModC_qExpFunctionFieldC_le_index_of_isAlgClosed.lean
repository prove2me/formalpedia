-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
-- name    : ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/e74ce629-34ea-5eff-a050-b72ab8f2cd60
-- title:
--   Deuring's inequality for the q-expansion function field over K(jmath̄)
-- statement:
--   Let $K$ be an algebraically closed field, let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, and let $\Gamma'$ be a subgroup with $\Gamma \le \Gamma'$ such that every $\gamma \in \Gamma'$ satisfies $\gamma \in \Gamma$ or $-\gamma \in \Gamma$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the field of Laurent series $K((q))$ generated over $K$ by the set of quotients $\overline{p_f}/\overline{p_g}$, where for some weight $k$ there are modular forms $f, g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and power series $p_f, p_g$ over $\mathbb{Z}$ that are integral $q$-expansions of $f$ and of $g$ (in the sense of the predicate `IsIntegralQExp`), the coefficientwise reduction $\overline{p_g}$ into $K$ being nonzero; here $\overline{p}$ denotes [`ModularCurve.intSeriesC K p`](def/ModularCurve_X1.html#L69). Let $x \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the reduction into $K$ of the integral power series $E_4^3 \cdot \eta^{-24}$-numerator `jNum` of the $j$-invariant. Then $F$ is a finite extension of the subfield $K(x)$ generated over $K$ by $x$, and $[F : K(x)] \le [\mathrm{SL}_2(\mathbb{Z}) : \Gamma']$.
--
--   This is Deuring's reduction inequality for the $q$-expansion function field of level $\Gamma$: over an arbitrary algebraically closed constant field the degree over $K(\bar\jmath)$ is bounded by the index of a subgroup squeezed between $\Gamma$ and $\pm\Gamma$, the classical equality $[\,\overline{\mathbb{Q}}(j,\dots) : \overline{\mathbb{Q}}(j)\,] = [\mathrm{PSL}_2(\mathbb{Z}) : \bar\Gamma]$ in characteristic $0$ specialising only to an inequality after reduction. It feeds the exact degree computations for $\Gamma_0(N)$ and $\Gamma_1(N)$ and the criterion for membership in the full modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
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
