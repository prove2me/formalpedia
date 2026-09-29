-- Prove2me | Theorems.Thm_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top
-- name    : LinearMap.exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/17d36a09-c416-5320-9d02-31e285d0544b
-- title:
--   Nakayama: injective map with 𝔪-divisible cokernel is an isomorphism on coinvariants
-- statement:
--   Let $R$ be a commutative ring, $\mathfrak m \subseteq R$ an ideal, and let $Y$ and $L$ be $R$-modules (abelian groups with $R$-module structures). Let $f \colon Y \to L$ be an $R$-linear map which is injective as a function, and suppose the quotient $L / \operatorname{range} f$ is a finite (i.e. finitely generated) $R$-module satisfying $\mathfrak m \cdot \top = \top$ as submodules of $L/\operatorname{range} f$, that is, $\mathfrak m (L/f(Y)) = L/f(Y)$. The conclusion is a conjunction. First, there exists an $R$-linear equivalence $e \colon Y/(\mathfrak m \cdot \top) \to L/(\mathfrak m \cdot \top)$, between the quotients of $Y$ and of $L$ by the submodules $\mathfrak m Y$ and $\mathfrak m L$ respectively, such that for every $y \in Y$ the class of $y$ is sent to the class of $f(y)$; thus $e$ is the map induced by $f$ on $\mathfrak m$-coinvariants. Second, the $(R/\mathfrak m)$-module ranks agree: $\operatorname{finrank}_{R/\mathfrak m}(Y/\mathfrak m Y) = \operatorname{finrank}_{R/\mathfrak m}(L/\mathfrak m L)$. No maximality of $\mathfrak m$, and no finiteness of $Y$ or $L$, is assumed.
--
--   This is a form of Nakayama's lemma: an injective map whose cokernel is finitely generated and equal to its own $\mathfrak m$-multiple becomes an isomorphism after passing to $\mathfrak m$-coinvariants, with the consequent equality of dimensions over $R/\mathfrak m$. It is used in the comparison of monodromy parts on modular curves, where the rank over a residue ring of a span must be transported between a submodule and the ambient module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top
    {R : Type*} [CommRing R] (𝔪 : Ideal R)
    {Y L : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L]
    (f : Y →ₗ[R] L) (hf : Function.Injective f)
    [Module.Finite R (L ⧸ LinearMap.range f)]
    (hC : (𝔪 • ⊤ : Submodule R (L ⧸ LinearMap.range f)) = ⊤) :
    (∃ e : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) ≃ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)),
        ∀ y : Y, e (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)) ∧
    Module.finrank (R ⧸ 𝔪) (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) = Module.finrank (R ⧸ 𝔪) (L ⧸ (𝔪 • ⊤ : Submodule R L)) := by sorry
