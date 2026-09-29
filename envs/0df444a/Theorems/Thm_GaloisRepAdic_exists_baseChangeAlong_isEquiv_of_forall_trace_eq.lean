-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq
-- name    : GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_forall_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/37e56bf0-9540-59ed-aedf-a32cd40d8d15
-- title:
--   Carayol descent of Galois representations to T, semi-local form
-- statement:
--   Let $T$ be a noetherian local ring, complete with respect to its maximal ideal and with finite residue field. Let $n\in\mathbb N$ and let $A_0,\dots,A_{n-1}$ be local rings, each a $T$-algebra that is finite as a $T$-module and whose structure map $T\to A_i$ is local, and assume the family is jointly injective: an element of $T$ whose image in every $A_i$ vanishes is $0$. Let $\bar\rho$ be a residual representation over the residue field $k_T$ of $T$, that is, a two-dimensional $k_T$-vector space with a monoid homomorphism from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to its endomorphisms which is trivial on the elements fixing some finite subextension $L/\mathbb Q$ of $\overline{\mathbb Q}$; assume $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline{k_T}$ has no invariant subspace other than $\bot$ and $\top$. For each $i$ let $\rho_i$ be a representation over $A_i$: a finite free $A_i$-module of rank $2$ with a monoid homomorphism $\rho_i$ to its $A_i$-endomorphisms such that for every $m$ there is a finite subextension $L/\mathbb Q$ with $\rho_i(\sigma)v-v\in\mathfrak m_{A_i}^m\cdot V_i$ for all $v$ and all $\sigma$ fixing $L$ pointwise. Assume each residual representation $k_{A_i}\otimes_{A_i}V_i$ of $\rho_i$ is equivalent, by an $k_{A_i}$-linear isomorphism commuting with the actions, to the base change of $\bar\rho$ along the induced map $k_T\to k_{A_i}$. Finally let $\tau$ be a function from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $T$ with $\operatorname{tr}\rho_i(\sigma)$ equal to the image of $\tau(\sigma)$ in $A_i$ for all $\sigma$ and all $i$ (no continuity is assumed of $\tau$). Then there exists a representation $\rho'$ over $T$, of the same shape (free of rank $2$, adically continuous), such that for every $i$ the base change $A_i\otimes_T\rho'$ is equivalent to $\rho_i$. The conclusion asserts only this existence; it does not record that the traces of $\rho'$ are given by $\tau$.
--
--   This is Carayol's descent theorem in a semi-local form: two-dimensional representations over a finite family of module-finite local $T$-algebras, with a common absolutely irreducible reduction and with all traces coming from $T$, descend to $T$ up to base change. It is the analytic-free ingredient behind [`GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective`](thm.html#GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective), where, via Chebotarev, only the traces of Frobenius elements need be prescribed, and thus behind the construction of Galois representations attached to Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_forall_trace_eq
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → T)
    (htr : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      (ρ i).trace σ = algebraMap T (A i) (τ σ)) :
    ∃ ρ' : GaloisRepAdic T,
      ∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i)) := by sorry
