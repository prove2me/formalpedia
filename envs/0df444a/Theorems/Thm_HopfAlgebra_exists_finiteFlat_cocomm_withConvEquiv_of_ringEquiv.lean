-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
-- name    : HopfAlgebra.exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/edaa75b8-6a58-5145-820d-f96661e1fa92
-- title:
--   Transport of finite flat cocommutative Hopf models along ring isomorphisms
-- statement:
--   Let $R$ and $S$ be commutative rings and $\varphi\colon R\xrightarrow{\sim} S$ a ring isomorphism, and suppose both $R$ and $S$ are equipped with algebra structures on $\overline{\mathbb{Q}}=\mathtt{AlgebraicClosure }\mathbb{Q}$ that are compatible with $\varphi$, in the sense that $\mathrm{algebraMap}_R(r)=\mathrm{algebraMap}_S(\varphi r)$ for all $r\in R$. Let $N$ be an additive commutative group carrying a distributive multiplicative action of the group $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Let $H$ be a commutative ring with a Hopf $S$-algebra structure that is finite and flat as an $S$-module and whose comultiplication is cocommutative, and let $e_H$ be a bijection from $\mathrm{WithConv}(H\to_{\mathrm{alg}[S]}\overline{\mathbb{Q}})$, the set of $S$-algebra maps $H\to\overline{\mathbb{Q}}$ with its convolution multiplication, onto $N$ such that $e_H(f\ast g)=e_H(f)+e_H(g)$, and such that whenever $g(h)=\sigma(f(h))$ for all $h\in H$ one has $e_H(g)=\sigma\cdot e_H(f)$. The conclusion asserts the existence of a type $H'$ with a commutative ring structure and a Hopf $R$-algebra structure, finite and flat as an $R$-module and cocommutative, together with a bijection $e'\colon\mathrm{WithConv}(H'\to_{\mathrm{alg}[R]}\overline{\mathbb{Q}})\to N$ satisfying the same two properties: additivity on convolution products, and the same equivariance condition for every $\sigma$.
--
--   This is the transport, along an isomorphism of base rings compatible with the chosen embeddings into $\overline{\mathbb{Q}}$, of a finite flat cocommutative Hopf-algebra model of a Galois module, together with the identification of its $\overline{\mathbb{Q}}$-points with $N$ as an $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$-module. It is bookkeeping used in the construction of finite flat models, and is cited by [`HopfAlgebra.exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq`](thm.html#HopfAlgebra.exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
    (R : Type) [CommRing R] (S : Type) [CommRing S] (φ : R ≃+* S)
    [Algebra R (AlgebraicClosure ℚ)] [Algebra S (AlgebraicClosure ℚ)]
    (hφ : ∀ r, algebraMap R (AlgebraicClosure ℚ) r = algebraMap S (AlgebraicClosure ℚ) (φ r))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra S H]
    (hHfin : Module.Finite S H) (hHflat : Module.Flat S H)
    (hHcocomm : Coalgebra.IsCocomm S H)
    (eH : WithConv (H →ₐ[S] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[S] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by sorry
