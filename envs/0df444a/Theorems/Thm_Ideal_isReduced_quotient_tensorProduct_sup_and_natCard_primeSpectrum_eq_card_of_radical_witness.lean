-- Prove2me | Theorems.Thm_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
-- name    : Ideal.isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/cf78e97b-f145-522a-a480-ecfdcd42511a
-- title:
--   Reducedness and component count of a crossing from a radical witness
-- statement:
--   Let $p$ be a prime, let $A$ be a Noetherian integrally closed domain of characteristic $0$, and let $\mathfrak p_\infty,\mathfrak p_0\subset A$ be prime ideals with $p\in\mathfrak p_\infty$ and such that every prime ideal of $A$ containing $p$ contains $\mathfrak p_\infty$ or contains $\mathfrak p_0$. Let $j,j_p,u,v\in A$ satisfy $uv=p^{12}$, $u\in\mathfrak p_0$ and $u\notin\mathfrak p_\infty$. Let $\kappa$ be a field of characteristic $p$, write $B=A\otimes_{\mathbf Z}\kappa$, and let $\mathfrak p B$ denote the image of an ideal $\mathfrak p$ of $A$ under the ring homomorphism $a\mapsto a\otimes 1$. Let $\theta:B\to\kappa[X]$ be a surjective ring homomorphism whose kernel is $\mathfrak p_\infty B$ and which satisfies $\theta(j\otimes 1)=X$ and $\theta(j_p\otimes 1)=X^p$, and assume $j-j_p^{\,p}\in\mathfrak p_0$. Assume finally that for a finite set $S\subset\kappa$, a function $n:\kappa\to\mathbf N$ with $n_a>0$ for all $a\in S$, and a nonzero $c\in\kappa$, one has $\theta(u\otimes 1)=c\prod_{a\in S}(X-a)^{n_a}$. Then the quotient ring $B/(\mathfrak p_\infty B+\mathfrak p_0 B)$ is reduced, and the number of points of its prime spectrum equals the cardinality of $S$.
--
--   This is the commutative algebra underlying the description of the geometric fibre at $p$ of the Deligne–Rapoport model of $X_0(p)$: the two primes $\mathfrak p_\infty,\mathfrak p_0$ correspond to the two components through the cusps $\infty$ and $0$, $u$ plays the role of Ogg's unit $\Delta(q)/\Delta(q^p)$, and the conclusion counts the crossing points of the two components and shows the crossing locus is reduced. It is used in the construction of the model of $X_0(p)$ over $\mathbf Z$ together with the identification of its fibre at $p$, via the fact that associated primes of a nonzero principal ideal in a Noetherian normal domain have height one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial TensorProduct

universe u v

theorem Ideal.isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    (𝔭inf 𝔭zero : Ideal A) [𝔭inf.IsPrime] [𝔭zero.IsPrime]
    (hpinf : (p : A) ∈ 𝔭inf)
    (hcover : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → (p : A) ∈ 𝔮 → 𝔭inf ≤ 𝔮 ∨ 𝔭zero ≤ 𝔮)
    (j jp u v : A) (huv : u * v = (p : A) ^ 12) (huzero : u ∈ 𝔭zero) (huinf : u ∉ 𝔭inf)
    (κ : Type v) [Field κ] [CharP κ p]
    (θ : A ⊗[ℤ] κ →+* κ[X]) (hθs : Function.Surjective θ)
    (hθk : RingHom.ker θ =
      𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))
    (hθj : θ (j ⊗ₜ 1) = X) (hθjp : θ (jp ⊗ₜ 1) = X ^ p)
    (hrel : j - jp ^ p ∈ 𝔭zero)
    (S : Finset κ) (n : κ → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : κ) (hc : c ≠ 0)
    (hθu : θ (u ⊗ₜ 1) = C c * ∏ a ∈ S, (X - C a) ^ n a) :
    IsReduced ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))) ∧
    Nat.card (PrimeSpectrum ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))))
      = S.card := by sorry
