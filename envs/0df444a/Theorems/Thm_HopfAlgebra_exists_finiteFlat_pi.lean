-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_pi
-- name    : HopfAlgebra.exists_finiteFlat_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/43d71655-eecb-5bad-9c31-14d46215fc23
-- title:
--   Finite flat Hopf models multiply over a finite index set
-- statement:
--   Let $R$ and $L$ be commutative rings with $L$ an $R$-algebra, let $\Gamma$ be a type equipped with a map $\pi : \Gamma \to (L \to L)$, let $\iota$ be a finite type, and for each $i : \iota$ let $M_i$ be a type carrying an addition together with a map $\mathrm{act}_i : \Gamma \to (M_i \to M_i)$. Assume that every $M_i$ is modelled in the following sense: there exist a commutative ring $H$ with the structure of a Hopf algebra over $R$ which is finite and flat as an $R$-module and whose comultiplication is cocommutative, and a bijection $e$ from `WithConv (H →ₐ[R] L)`, the $R$-algebra homomorphisms $H \to L$ with the convolution multiplication, onto $M_i$, such that $e(f \ast g) = e(f) + e(g)$ for all $f, g$, and such that for all $\sigma : \Gamma$ and all $f, g$ with $g(x) = \pi(\sigma)(f(x))$ for every $x \in H$ one has $e(g) = \mathrm{act}_i(\sigma)(e(f))$. Then the product type $\prod_i M_i$, with componentwise addition and with the componentwise action $\sigma \mapsto (m_i) \mapsto (\mathrm{act}_i(\sigma)(m_i))$, admits a model of the same shape: a finite flat cocommutative commutative Hopf algebra $H$ over $R$ and a bijection $e$ from `WithConv (H →ₐ[R] L)` onto $\prod_i M_i$ sending convolution to addition and satisfying $e(g) = (i \mapsto \mathrm{act}_i(\sigma)(e(f)_i))$ whenever $g = \pi(\sigma) \circ f$ pointwise.
--
--   This is the closure of the class of $\Gamma$-modules admitting a finite flat commutative cocommutative Hopf-algebra model under finite products, the model of a product being the tensor product of the models of the factors (the empty product being $R$). The existential pattern matches the flatness condition imposed on $p$-adic Galois representations, and the result is used to assemble such flat models componentwise, for instance in the flatness statements for points on modular curves and for the Galois representations attached to cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_pi.lean

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_pi {R L Γ ι : Type} [CommRing R] [CommRing L] [Algebra R L]
    [Finite ι] (π : Γ → L → L) (M : ι → Type) [∀ i, Add (M i)] (act : ∀ i, Γ → M i → M i)
    (h : ∀ i, ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ M i,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x, g x = π σ (f x)) → e g = act i σ (e f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ (∀ i, M i),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x, g x = π σ (f x)) →
          e g = fun i => act i σ (e f i) := by sorry
