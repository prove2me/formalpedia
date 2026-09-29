-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_coeffMap_of_linearIndependent
-- name    : ModularCurve.linearIndependent_coeffMap_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/8eaae00f-ca59-55b1-9540-3251f568fc7e
-- title:
--   Coefficient extension preserves linear independence of Laurent series
-- statement:
--   Let $\kappa_0$ and $K$ be fields and let $\varphi : \kappa_0 \to K$ be a ring homomorphism. Let $\iota$ be a finite index type and let $x : \iota \to \kappa_0(\!(q)\!)$ be a family of formal Laurent series over $\kappa_0$ (Hahn series over $\kappa_0$ with value group $\mathbb{Z}$) which is linearly independent over $\kappa_0$. The assertion is that the family $i \mapsto \mathtt{coeffMap}\,\varphi\,(x\,i)$ is linearly independent over $K$, where [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) is the ring homomorphism $\kappa_0(\!(q)\!) \to K(\!(q)\!)$ obtained by applying $\varphi$ to each coefficient. Concretely: if coefficients $c_i \in K$ satisfy $\sum_i c_i \cdot \varphi(x_i) = 0$ in $K(\!(q)\!)$, then all $c_i$ vanish. Here $K$ carries the $\kappa_0$-module structure coming from $\varphi$, and no hypothesis is placed on $\varphi$ beyond being a homomorphism of fields (so it is automatically injective) — in particular $K$ may be transcendental over the image of $\kappa_0$.
--
--   This is the statement that $\kappa_0(\!(q)\!)$ and $K$ are linearly disjoint over $\kappa_0$, i.e. that $\kappa_0(\!(q)\!) \otimes_{\kappa_0} K \to K(\!(q)\!)$ is injective. It is used in the analysis of chart algebras on modular curves, where it converts independence of reductions of $q$-expansions over a small coefficient field into independence over a larger one, so that membership of all $q$-coefficients in a maximal ideal forces membership of the individual scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_coeffMap_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.linearIndependent_coeffMap_of_linearIndependent
    (κ₀ K : Type) [Field κ₀] [Field K] (φ : κ₀ →+* K)
    (ι : Type) [Fintype ι] (x : ι → LaurentSeries κ₀) (hx : LinearIndependent κ₀ x) :
    LinearIndependent K (fun i => ModularCurve.coeffMap φ (x i)) := by sorry
