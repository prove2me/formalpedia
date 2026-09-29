-- Prove2me | Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
-- name    : ModularFormClass.eq_of_forall_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/fb97e0fa-1f4b-59f3-b303-c7736e494490
-- title:
--   A modular form is determined by its q-expansion
-- statement:
--   Let $F$ be a type equipped with a `FunLike F UpperHalfPlane ℂ` structure, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $k$ be an integer, and suppose $F$ carries a `ModularFormClass F Γ k` structure, so that its elements are interpreted as weight-$k$ modular forms on $\Gamma$. Let $f, g : F$. Assume that $1$ lies in `Γ.strictPeriods`, i.e. that $\Gamma$ contains the translation by $1$, so that the associated functions on the upper half-plane are invariant under $\tau \mapsto \tau + 1$ and admit $q$-expansions in $q = e^{2\pi i \tau}$. Assume further that for every natural number $n$ the $n$-th coefficients agree, $\mathrm{qCoeff}\ f\ n = \mathrm{qCoeff}\ g\ n$, where [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) of a function $\mathbb{H} \to \mathbb{C}$ at $n$ is by definition the $n$-th coefficient of its period-$1$ $q$-expansion `qExpansion 1`. The conclusion is the equality $f = g$ in $F$ itself, not merely the equality of the two functions on the upper half-plane.
--
--   This is the standard injectivity of the $q$-expansion map at $\infty$ for modular forms with period $1$ (for instance on $\Gamma_0(N)$ or $\Gamma_1(N)$), stated uniformly for any carrier of modular forms of weight $k$ on $\Gamma$, such as holomorphic modular forms or cusp forms. It is the basic tool by which forms are compared through their Fourier coefficients, and is used throughout the treatment of newforms, normalised eigenforms and integral structures on spaces of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.eq_of_forall_qCoeff_eq {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by sorry
