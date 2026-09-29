-- Prove2me | Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
-- name    : ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/d98e6416-da3e-517f-9bda-a6513d150a13
-- title:
--   Fricke involution sends the ∞-expansion to the 0-expansion
-- statement:
--   Let $\ell$ be a prime, let $f,g$ be Laurent series over $\mathbb{Q}$, and let $F\colon\mathfrak{H}\to\mathbb{C}$ be a function on the upper half-plane. Assume: (hF) for every $\tau$, the family $m\mapsto f_m\,q_1(\tau)^m$ indexed by $m\in\mathbb{Z}$, where $f_m$ is the $m$-th coefficient of $f$ mapped into $\mathbb{C}$ and $q_h(\tau)=e^{2\pi i\tau/h}$ is Mathlib's `Function.Periodic.qParam`, is summable with sum $F(\tau)$; (hG) for every $\tau$, the family $m\mapsto g_m\,q_\ell(\tau)^m$ is summable with sum $F(S\cdot\tau)$, where $S$ is the standard involution in $\mathrm{SL}_2(\mathbb{Z})$; (hinv) $F(\gamma\cdot\tau)=F(\tau)$ for all $\gamma\in\Gamma_0(\ell)$ and all $\tau$; and (hf) $f$ lies in `modularFunctionFieldFull ℓ`, the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of series $q\mapsto$ `qExpand ℚ d jq` for the nonzero divisors $d$ of $\ell$. The conclusion is that applying `frickeInvolutionFull ℓ` to the element $\langle f,\mathrm{hf}\rangle$ and taking the underlying Laurent series yields exactly $g$. Here `frickeInvolutionFull ℓ` is, by definition, a chosen $\mathbb{Q}$-algebra automorphism $\sigma$ of `modularFunctionFieldFull ℓ` satisfying `IsFrickeAutFull ℓ σ` — that is, $\sigma(\mathtt{qExpand}\ \mathbb{Q}\ a\ \mathtt{jq})=\mathtt{qExpand}\ \mathbb{Q}\ b\ \mathtt{jq}$ whenever $ab=\ell$ with $a,b$ nonzero — if such a $\sigma$ exists, and the identity automorphism otherwise; existence for primes is supplied by [`ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime`](thm.html#ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime).
--
--   This is the $q$-expansion form of the statement that the Fricke involution $w_\ell$ on the function field of $X_0(\ell)$ interchanges the cusps $\infty$ and $0$: a $\Gamma_0(\ell)$-invariant function with expansion $f$ at $\infty$ (period $1$) and expansion $g$ at $0$ (period $\ell$) has $w_\ell(f)=g$. It is used to identify the Fricke image of modular unit series and to place the resulting series in the modular function field, via [`ModularCurve.coe_frickeInvolutionFull_modularUnitSeries`](thm.html#ModularCurve.coe_frickeInvolutionFull_modularUnitSeries) and [`ModularCurve.sharpUnitSeries_mem_modularFunctionField`](thm.html#ModularCurve.sharpUnitSeries_mem_modularFunctionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ) (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ))) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) (hf : f ∈ ModularCurve.modularFunctionFieldFull ℓ) : ((ModularCurve.frickeInvolutionFull ℓ ⟨f, hf⟩ : ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = g := by sorry
