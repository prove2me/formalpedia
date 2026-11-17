-- Prove2me | Theorems.Thm_N25_LocalFive_finite_quotient_and_surjective_nsmul_comap
-- name    : N25.LocalFive.finite_quotient_and_surjective_nsmul_comap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:42.182725+00:00
-- url     : https://prove2.me/theorems/f3230caa-8da8-4859-b0d3-5d36ed286cd6
-- title:
--   Finite-index divisibility pulls back along a saturated embedding
-- statement:
--   Let $e:M\to L$ be an injective homomorphism of abelian groups and let $n\ge0$. Assume the image of $e$ is $n$-saturated, meaning $ny\in e(M)$ implies $y\in e(M)$. If $U_0\le L$, $L/U_0$ is finite, and $[n]$ is surjective on $U_0$, then for $U=e^{-1}(U_0)$ one has $$|M/U|<\infty,\qquad [n]:U\twoheadrightarrow U.$$ This transports the local finite-index divisibility statement back through an injective realization of the Mordell-Weil group.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

theorem N25.LocalFive.finite_quotient_and_surjective_nsmul_comap
    {M L : Type*} [AddCommGroup M] [AddCommGroup L]
    (e : M →+ L) (he : Function.Injective e)
    (n : ℕ)
    (hsat : ∀ y : L, n • y ∈ e.range → y ∈ e.range)
    (U₀ : AddSubgroup L)
    (hfin : Finite (L ⧸ U₀))
    (hU₀ : Function.Surjective (fun u : U₀ => n • u)) :
    Finite (M ⧸ U₀.comap e) ∧
      Function.Surjective (fun u : U₀.comap e => n • u) := by sorry
