-- Prove2me | Theorems.Thm_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero
-- name    : ModularCurve.Period.CuspForm.periodHom_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/f7178cce-526d-5f45-8e18-33601838c1bb
-- title:
--   Nonzero weight-2 cusp forms have nonzero period character
-- statement:
--   Let $N$ be a positive integer and let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$, assumed nonzero. Let $F_{\mathrm{prim}} : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is an equivariant primitive for $\Gamma_0(N)$ in the sense of the project, i.e. for every $\gamma \in \Gamma_0(N)$ there is a constant $c \in \mathbb{C}$ with $F_{\mathrm{prim}}(\gamma \cdot z) - F_{\mathrm{prim}}(z) = c$ for all $z \in \mathbb{H}$, and assume that $F_{\mathrm{prim}}$ is a primitive of $f$ in the analytic sense: for every $\tau \in \mathbb{H}$, the function $F_{\mathrm{prim}} \circ \mathrm{ofComplex}$ has complex derivative $f(\tau)$ at the point $\tau$ of $\mathbb{C}$. The conclusion is that the associated period homomorphism is nonzero, that is, the additive group homomorphism $\mathrm{Additive}\,\Gamma_0(N) \to \mathbb{C}$ sending $\gamma$ to the period $F_{\mathrm{prim}}(\gamma \cdot i) - F_{\mathrm{prim}}(i)$ (evaluation at the point $i$ of $\mathbb{H}$) is not the zero homomorphism.
--
--   This is the injectivity input for the period (Eichler–Shimura) map attached to weight-2 cusp forms on $\Gamma_0(N)$: a nonzero form has a nonzero period character on $\Gamma_0(N)$. It is used by [`ModularCurve.periodMap_injective`](thm.html#ModularCurve.periodMap_injective); note that it asserts only non-vanishing of the period character, not any dimension equality of Eichler–Shimura type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero.lean

import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.Period.CuspForm.periodHom_ne_zero_of_ne_zero {N : ℕ} [NeZero N]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ≠ 0)
    {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hFprim.periodHom ≠ 0 := by sorry
