-- Prove2me | Theorems.Thm_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple
-- name    : ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/9fdfd97e-65e3-5f29-a0cf-74b8534281a2
-- title:
--   Module-finite algebra representing Γ₀(M') kernel tuples
-- statement:
--   Let $B$ be a commutative ring in a universe $u$, let $W$ be a Weierstrass curve over $B$, let $M' : \mathbb{N}$, and assume that the product of the image of $M'$ in $B$ with the discriminant $W.\Delta$ is a unit of $B$. Then there exist a type $C$ in the same universe, a commutative ring structure on $C$, a $B$-algebra structure making $C$ a module-finite $B$-algebra, and a family $h^{u}$ of polynomials in $C[X]$ indexed by the prime factors of $M'$, such that for each prime $p \mid M'$ the base-changed curve $W$ over $C$ satisfies [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) at $p$ with exponent $k_p = \mathrm{ord}_p(M')$ and polynomial $h^{u}_p$ — that is, if $p^{k_p} = 2$ then $h^u_p$ has degree at most $1$, coefficient $1$ in degree $1$, and divides $\Psi_2^2$ of the curve, and otherwise $h^u_p$ has degree at most $\varphi(p^{k_p})/2$, coefficient $1$ in that degree, $h^u_p \cdot \mathrm{pre}\Psi(p^{k_p-1})$ divides $\mathrm{pre}\Psi(p^{k_p})$, and $h^u_p$ divides $\mathrm{smulNumerator}\,a\,(\varphi(p^{k_p})/2)\,h^u_p$ for every $a$ with $2 \le a \le (p^{k_p}-1)/2$ and $p \nmid a$ — and such that this datum is universal: for every commutative ring $T$ in universe $u$, every ring homomorphism $\varphi : B \to T$ and every family $h$ of polynomials in $T[X]$ indexed by the prime factors of $M'$, the family satisfies these same conditions at every $p \mid M'$ for the curve $W$ base-changed along $\varphi$ if and only if there is a unique ring homomorphism $\psi : C \to T$ with $\psi \circ (\text{structure map } B \to C) = \varphi$ whose coefficientwise image of $h^{u}$ is, as a family, equal to $h$.
--
--   This is the representability statement for $\Gamma_0(M')$-level structures on a fixed Weierstrass curve with $M'\Delta$ invertible, in the style of Katz–Mazur's treatment of level structures: the functor of tuples of monic generator-kernel polynomials, one for each prime power exactly dividing $M'$, is represented by a module-finite $B$-algebra. It is obtained by combining the prime-power cases [`WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents`](thm.html#WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents) and [`WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents`](thm.html#WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents), and feeds the construction of the level moduli packages for $\Gamma_0$, $\Gamma_1$ and full level used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (M' : ℕ)
    (hu : IsUnit (((M' : ℕ) : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C)
      (hᵤ : ↥M'.primeFactors → Polynomial C)
      (_ : ∀ p : ↥M'.primeFactors,
        ModularCurve.IsGamma0PowAt (W.map (algebraMap B C)) (p : ℕ) (M'.factorization (p : ℕ)) (hᵤ p)),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (hh : ↥M'.primeFactors → Polynomial T),
        (∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (W.map φ) (p : ℕ) (M'.factorization (p : ℕ)) (hh p)) ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ (fun p => (hᵤ p).map ψ) = hh := by sorry
