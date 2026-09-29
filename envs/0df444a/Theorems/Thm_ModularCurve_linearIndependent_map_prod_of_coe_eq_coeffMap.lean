-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
-- name    : ModularCurve.linearIndependent_map_prod_of_coe_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/6733ecaa-8db4-59ab-ae76-d4a8f53a8415
-- title:
--   Coefficientwise base change preserves independence of pairs
-- statement:
--   Let $k_0$ and $k$ be fields and $\sigma : k_0 \to k$ a ring homomorphism. Let $F_0$ be an intermediate field of the extension $k_0 \subseteq k_0((\mathfrak q))$ of the field of formal Laurent series over $k_0$, and let $F$ be an intermediate field of $k \subseteq k((\mathfrak q))$. Let $\iota : F_0 \to F$ be a ring homomorphism which acts coefficientwise through $\sigma$, in the sense that for every $x \in F_0$ the Laurent series underlying $\iota(x)$ is `coeffMap` $\sigma$ applied to the Laurent series underlying $x$, that is, the series obtained by applying $\sigma$ to each coefficient of $x$. Let $n$ be a natural number and $v : \mathrm{Fin}\,n \to F_0 \times F_0$ a family of pairs which is linearly independent over $k_0$. Then the family $j \mapsto (\iota (v_j)_1, \iota (v_j)_2)$ of pairs in $F \times F$ is linearly independent over $k$. No injectivity hypothesis is imposed on $\sigma$ or on $\iota$ beyond what the field structures force.
--
--   This is the form of linear disjointness used when constants are reduced: a $k_0$-independent family of pairs of $q$-expansions stays independent over the larger or residual constant field $k$. It is applied in the construction of functions in Riemann–Roch spaces with prescribed residues and ordinary behaviour at prolonged places on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open ModularCurve

theorem ModularCurve.linearIndependent_map_prod_of_coe_eq_coeffMap
    {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : F₀ →+* F) (hι : ∀ x : F₀, ((ι x : F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))
    {n : ℕ} {v : Fin n → F₀ × F₀} (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun j => ((ι (v j).1 : F), (ι (v j).2 : F))) := by sorry
