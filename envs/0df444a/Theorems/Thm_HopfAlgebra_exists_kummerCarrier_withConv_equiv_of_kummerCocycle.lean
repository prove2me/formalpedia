-- Prove2me | Theorems.Thm_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle
-- name    : HopfAlgebra.exists_kummerCarrier_withConv_equiv_of_kummerCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/27450205-73ed-556b-b005-9e30081bb36f
-- title:
--   Kummer carrier Hopf algebra of a Kummer cocycle datum
-- statement:
--   Let $O$ be a non-trivial commutative ring, let $p$ be a prime and $N$ a natural number, and let $\Lambda$ be a finite additive abelian group. Let $u:\Lambda\to O$ take unit values, with $u_0=1$, and let $c:\Lambda\times\Lambda\to O$ satisfy $c_{\lambda\lambda'}^{\,p^N}\,(u_\lambda u_{\lambda'})=u_{\lambda+\lambda'}$, $c_{0\lambda}=1$, $c_{\lambda\lambda'}=c_{\lambda'\lambda}$ and $c_{\lambda\lambda'}c_{\lambda+\lambda',\lambda''}=c_{\lambda,\lambda'+\lambda''}c_{\lambda'\lambda''}$ for all $\lambda,\lambda',\lambda''$. The assertion is that there exist a type $H$ with a commutative ring structure and a Hopf $O$-algebra structure such that $H$ is finite and free as an $O$-module, its comultiplication is cocommutative, $\operatorname{finrank}_O H=p^N\cdot|\Lambda|$, and the following holds for every commutative ring $L$ which is a domain and an $O$-algebra: given $\zeta\in L$ a primitive $p^N$-th root of unity and $\eta:\Lambda\to L$ with $\eta_\lambda^{\,p^N}$ the image of $u_\lambda$ in $L$, $\eta_0=1$ and $\eta_{\lambda+\lambda'}=c_{\lambda\lambda'}\,\eta_\lambda\eta_{\lambda'}$, there is a bijection $\psi$ from $\mathbb{Z}/p^N\times\Lambda$ onto the set of $O$-algebra homomorphisms $H\to L$, viewed through `WithConv` with its convolution multiplication, which carries addition to convolution, $\psi(a+b)=\psi(a)\psi(b)$, and which is equivariant in the following sense: for every $O$-algebra endomorphism $\tau$ of $L$ and all $e\in\mathbb{N}$, $\kappa:\Lambda\to\mathbb{N}$ with $\tau\zeta=\zeta^e$ and $\tau(\eta_\lambda)=\zeta^{\kappa_\lambda}\eta_\lambda$ for all $\lambda$, one has $\psi(e\,i+\kappa_\lambda,\lambda)(h)=\tau\bigl(\psi(i,\lambda)(h)\bigr)$ for all $i\in\mathbb{Z}/p^N$, $\lambda\in\Lambda$ and $h\in H$.
--
--   This is the existence statement for the Kummer carrier attached to a Kummer cocycle datum $(u,c)$: a finite free commutative cocommutative Hopf $O$-algebra of rank $p^N|\Lambda|$, representing an extension of the constant group $\Lambda$ by $\mu_{p^N}$ with the prescribed unit radicands, together with an explicit Galois-equivariant parametrisation of its $L$-points by $\mathbb{Z}/p^N\times\Lambda$. It is used by [`HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level`](thm.html#HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_kummerCarrier_withConv_equiv_of_kummerCocycle
    (O : Type) [CommRing O] [Nontrivial O] (p N : ℕ) [Fact p.Prime]
    (Λ : Type) [AddCommGroup Λ] [Finite Λ]
    (u : Λ → O) (hu : ∀ l : Λ, IsUnit (u l)) (hu0 : u 0 = 1)
    (c : Λ → Λ → O)
    (hc : ∀ l l' : Λ, c l l' ^ (p ^ N) * (u l * u l') = u (l + l'))
    (hc0 : ∀ l : Λ, c 0 l = 1) (hcomm : ∀ l l' : Λ, c l l' = c l' l)
    (hassoc : ∀ l l' l'' : Λ, c l l' * c (l + l') l'' = c l (l' + l'') * c l' l'') :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra O H),
      Module.Finite O H ∧ Module.Free O H ∧ Coalgebra.IsCocomm O H ∧
      Module.finrank O H = p ^ N * Nat.card Λ ∧
      ∀ (L : Type) [CommRing L] [IsDomain L] [Algebra O L] (ζ : L), IsPrimitiveRoot ζ (p ^ N) →
        ∀ η : Λ → L, (∀ l, η l ^ (p ^ N) = algebraMap O L (u l)) → η 0 = 1 →
          (∀ l l', η (l + l') = algebraMap O L (c l l') * η l * η l') →
          ∃ ψ : ZMod (p ^ N) × Λ ≃ WithConv (H →ₐ[O] L),
            (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
            ∀ (τ : L →ₐ[O] L) (e : ℕ) (κ : Λ → ℕ), τ ζ = ζ ^ e → (∀ l, τ (η l) = ζ ^ κ l * η l) →
              ∀ (i : ZMod (p ^ N)) (l : Λ) (h : H), ψ (e • i + (κ l : ZMod (p ^ N)), l) h = τ (ψ (i, l) h) := by sorry
