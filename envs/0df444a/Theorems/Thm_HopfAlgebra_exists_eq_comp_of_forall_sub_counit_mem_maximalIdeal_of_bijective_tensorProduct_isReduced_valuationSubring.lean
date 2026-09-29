-- Prove2me | Theorems.Thm_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
-- name    : HopfAlgebra.exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a90dacd7-8db7-56f5-bb68-2a42866ca373
-- title:
--   Formal P-points factor through the multiplicative quotient
-- statement:
--   Let $p$ be a prime, let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ which is henselian as a local ring and satisfies $p \in \mathfrak{m}_P$, and write $k = \mathrm{ResidueField}\,P$. Let $A$ be a commutative ring carrying a cocommutative Hopf $P$-algebra structure, finite and free as a $P$-module with $\operatorname{finrank}_P A = p^n$ for some $n$, and let $M$ be another commutative ring with a cocommutative Hopf $P$-algebra structure, finite free over $P$, together with a surjective bialgebra homomorphism $\pi : A \to M$. Assume the Cartier dual $\mathrm{CartierDual}\,P\,M$ (the $P$-module dual of $M$ with its convolution algebra structure) is étale over $P$, and assume the following base-change hypothesis: for every henselian local commutative $P$-algebra $R'$ whose structure map is a local homomorphism, $\mathrm{CartierDual}\,R'\,(R' \otimes_P M)$ is étale over $R'$, and for every cocommutative Hopf $R'$-algebra $N$, finite free over $R'$ with étale Cartier dual, every bialgebra homomorphism $R' \otimes_P A \to N$ factors uniquely through $\mathrm{id} \otimes \pi$. Assume further that the special fibre is ordinary in the sense that there exist a finite free cocommutative-free-of-hypothesis Hopf $k$-algebra $M_0$ (a commutative ring, finite free over $k$), a Hopf $k$-algebra $E_0$, and a bijective bialgebra homomorphism $\Theta : k \otimes_P A \to M_0 \otimes_k E_0$ with $E_0$ reduced and $\mathrm{CartierDual}\,k\,M_0$ reduced. Then every $P$-algebra homomorphism $f : A \to P$ with $f(a) - \varepsilon(a) \in \mathfrak{m}_P$ for all $a \in A$ factors as $f = g \circ \pi$ for some $P$-algebra homomorphism $g : M \to P$.
--
--   In the language of group schemes: over the valuation ring of a place of $\overline{\mathbb{Q}}$ above $p$, the formal ($\equiv$ identity modulo $\mathfrak{m}_P$) points of a finite flat $p$-group with ordinary special fibre are exactly the points of its multiplicative-type quotient, obtained by comparing the number of points of the group, of its special fibre and of the quotient. It feeds the computation of the Cartier-duality pairing on points of $p$-divisible groups used later in the ordinary-deformation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) [HenselianLocalRing P]
    (hp : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (A : Type) [CommRing A] [HopfAlgebra P A] [Coalgebra.IsCocomm P A]
    [Module.Finite P A] [Module.Free P A]
    (hA : ∃ n : ℕ, Module.finrank P A = p ^ n)

    (M : Type) [CommRing M] [HopfAlgebra P M] [Coalgebra.IsCocomm P M] [Module.Free P M] [Module.Finite P M]
    (π : A →ₐc[P] M) (hπ : Function.Surjective π) (hMet : Algebra.Etale P (CartierDual P M))
    (hμbc : (∀ (R' : Type) [CommRing R'] [HenselianLocalRing R'] [Algebra P R'],
          IsLocalHom (algebraMap P R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[P] M)) ∧
          ∀ (N : Type) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[P] A →ₐc[R'] N),
              ∃! g : R' ⊗[P] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f))

    (hord : ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] A →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀))
    (f : A →ₐ[P] P) (hf : ∀ a : A, f a - Coalgebra.counit (R := P) a ∈ IsLocalRing.maximalIdeal P) :
    ∃ g : M →ₐ[P] P, f = g.comp (π : A →ₐ[P] M) := by sorry
