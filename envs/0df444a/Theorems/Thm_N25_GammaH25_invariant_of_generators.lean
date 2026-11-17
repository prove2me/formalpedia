-- Prove2me | Theorems.Thm_N25_GammaH25_invariant_of_generators
-- name    : N25.GammaH25_invariant_of_generators
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:58.139722+00:00
-- url     : https://prove2.me/theorems/0d8884a0-a551-4fa8-95ea-30d909812103
-- title:
--   Invariance under $\Gamma_1(25)$ and one lift implies $\Gamma_H(25)$-invariance
-- statement:
--   Let $T\in\Gamma_0(25)$ have lower-right unit label $7^{-1}$ modulo $25$, and let $f:\mathfrak H\to\mathbf C$ be a function on the upper half-plane. Assume $f(A\tau)=f(\tau)$ for every $A\in\Gamma_1(25)$ and every $\tau\in\mathfrak H$, and assume $f(T\tau)=f(\tau)$ for every $\tau$. Then, for every $A\in\Gamma_H(25)$ and every $\tau\in\mathfrak H$,
--
--   $$f(A\tau)=f(\tau).$$
--
--   This promotes invariance under the stated generators to invariance under the full level subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open CongruenceSubgroup
open N25

theorem N25.GammaH25_invariant_of_generators (T : Gamma0 25)
    (hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 7 (by decide))⁻¹)
    (f : UpperHalfPlane → ℂ)
    (h1 : ∀ A ∈ Gamma1 25, ∀ τ : UpperHalfPlane, f (A • τ) = f τ)
    (hgen : ∀ τ : UpperHalfPlane, f ((T : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = f τ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CohCarrier.GammaH 25 N25.H25) (τ : UpperHalfPlane) :
    f (A • τ) = f τ := by sorry
