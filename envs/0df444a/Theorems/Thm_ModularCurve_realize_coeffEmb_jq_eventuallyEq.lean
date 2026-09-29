-- Prove2me | Theorems.Thm_ModularCurve_realize_coeffEmb_jq_eventuallyEq
-- name    : ModularCurve.realize_coeffEmb_jq_eventuallyEq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/87c307a3-3dcc-5062-a74a-b77e7e1957d5
-- title:
--   Realisation of jmatĥ equals E₄³/Δ near every point
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $\tau$ be a point of the upper half-plane $\mathfrak H$. Consider the Laurent series over $\mathbb{C}$ obtained by applying [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) — coefficientwise application of the structure map $\mathbb{Q} \to \mathbb{C}$ — to [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the rational Laurent series $q^{-1}$ times the power series `jNumQ` (the $\mathbb{Q}$-coefficient form of the numerator of $j$). For a Laurent series $x$ over $\mathbb{C}$, [`ModularCurve.realize N x`](def/ModularCurve_ComplexPlaceDictionary.html#L17) evaluates as follows at a point of $\mathfrak H$: if there exists a weight $k \in \mathbb{Z}$ and a pair $(g,h)$ of modular forms of weight $k$ on $\Gamma_0(N)$ with $h$ nonvanishing at that point and $x \cdot \widetilde{h} = \widetilde{g}$ as Laurent series, where $\widetilde{\,\cdot\,}$ denotes the $q$-expansion of period $1$ regarded in $\mathbb{C}((q))$, the value is $g/h$ at that point for some such chosen pair; otherwise the value is $0$. The assertion is that the functions $z \mapsto \mathrm{realize}_N(\hat\jmath)(\mathrm{ofComplex}\, z)$ and $z \mapsto E_4(\mathrm{ofComplex}\, z)^3 / \Delta(\mathrm{ofComplex}\, z)$ of a complex variable $z$ agree eventually along the punctured neighbourhood filter $\mathcal{N}[\neq](\tau)$ of $\tau$ in $\mathbb{C}$, where $E_4$ and $\Delta$ are Mathlib's level-one Eisenstein series of weight $4$ and the discriminant cusp form.
--
--   This identifies the function on $\mathfrak H$ realised by the $q$-expansion of the modular invariant at level $N$ with the classical expression $E_4^3/\Delta$ for $j$, off a discrete set. It is used in establishing that `coeffEmb ℂ jq` belongs to the point data of a complex place dictionary for $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_realize_coeffEmb_jq_eventuallyEq.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open UpperHalfPlane

theorem ModularCurve.realize_coeffEmb_jq_eventuallyEq (N : ℕ) [NeZero N] (τ : ℍ) :
    (fun z : ℂ => ModularCurve.realize N (ModularCurve.coeffEmb ℂ ModularCurve.jq) (ofComplex z))
      =ᶠ[nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ]
      fun z : ℂ => ModularForm.E₄ (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z) := by sorry
