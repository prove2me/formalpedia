-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_realize_eventuallyEq_div
-- name    : ModularCurve.exists_modularForm_realize_eventuallyEq_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c5fd6e00-4ee1-5ca4-855e-686aa03f971f
-- title:
--   Modular functions are locally quotients g/h of modular forms
-- statement:
--   Let $N\ge 1$ be a natural number and let $x$ be an element of the subfield [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) of $\mathbb C(\!(q)\!)$, that is, of the intermediate field generated over $\mathbb{C}$ by the images, under the coefficientwise extension $\mathbb Q(\!(q)\!)\to\mathbb C(\!(q)\!)$ of $\mathbb Q\hookrightarrow\mathbb C$, of the elements of the subfield of $\mathbb Q(\!(q)\!)$ generated over $\mathbb Q$ by the series $\mathrm{qExpand}\,\mathbb Q\,d\,jq$ for the nonzero divisors $d$ of $N$. Then there are an integer $k$ and modular forms $g,h$ of weight $k$ on $\Gamma_0(N)$ with $h\neq 0$ such that, writing $\tilde f$ for the $q$-expansion at width $1$ of a form $f$, one has the identity $x\cdot\tilde h=\tilde g$ in $\mathbb C(\!(q)\!)$, and such that for every $\tau$ in the upper half-plane the two functions $z\mapsto \mathrm{realize}\,N\,x\,(\mathrm{ofComplex}\,z)$ and $z\mapsto g(\mathrm{ofComplex}\,z)/h(\mathrm{ofComplex}\,z)$ on $\mathbb C$ agree on a punctured neighbourhood of $\tau$ (equality along the filter $\mathcal N_{\neq}(\tau)$), where `ofComplex` is the retraction of $\mathbb C$ onto $\mathbb H$. Here $\mathrm{realize}\,N\,x\,\tau$ is defined to be $g'(\tau)/h'(\tau)$ for some choice of weight-$k'$ forms $g',h'$ on $\Gamma_0(N)$ with $h'(\tau)\neq 0$ and $x\cdot\tilde{h'}=\tilde{g'}$, when such a triple exists, and $0$ otherwise.
--
--   This is the dictionary between the $q$-expansion presentation of the function field of $X_0(N)$ over $\mathbb C$ and the analytic picture on the upper half-plane: an element of that field is globally a ratio of $q$-expansions of two modular forms of a common weight on $\Gamma_0(N)$, and its pointwise realisation as a function on $\mathbb H$ coincides with the corresponding quotient $g/h$ near every point. It is used to derive analyticity and local behaviour of realisations, and in the estimates for hyperplane sections on $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_realize_eventuallyEq_div.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_modularForm_realize_eventuallyEq_div (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ∧
      ∀ τ : ℍ, (fun z : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by sorry
