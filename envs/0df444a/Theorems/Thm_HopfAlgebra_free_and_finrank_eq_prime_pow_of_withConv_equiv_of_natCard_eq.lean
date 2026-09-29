-- Prove2me | Theorems.Thm_HopfAlgebra_free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq
-- name    : HopfAlgebra.free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3fbc3cfc-eff2-55a1-bc9c-123a7b661006
-- title:
--   Finite flat Hopf algebra over ℤₚ with pᵃ points is free of rank pᵃ
-- statement:
--   Let $p$ be a prime and let $H$ be a commutative ring carrying the structure of a Hopf algebra over the $p$-adic integers $\mathbb{Z}_p$ which, as a $\mathbb{Z}_p$-module, is finite (finitely generated) and flat, and whose comultiplication is cocommutative. Let $\mathrm{PadicAlgCl}\,p$ denote the fixed algebraic closure of $\mathbb{Q}_p$, an algebraically closed field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Suppose given a finite type $M$, a bijection $e$ between $M$ and the type `WithConv` $(H \to_{\mathrm{alg}[\mathbb{Z}_p]} \mathrm{PadicAlgCl}\,p)$ — the type synonym, with the same underlying elements, of the set of $\mathbb{Z}_p$-algebra homomorphisms from $H$ to this algebraic closure — and a natural number $a$ with $\#M = p^a$. The conclusion is twofold: $H$ is a free $\mathbb{Z}_p$-module, and its rank over $\mathbb{Z}_p$ equals $p^a$.
--
--   This is the passage from a count of geometric points of a finite flat commutative group scheme over $\mathbb{Z}_p$ to the rank of its coordinate ring, the classical input being that a finite Hopf algebra over a field of characteristic zero is étale, so that its dimension is the number of its geometric points. It is used in the construction of a unipotent model, [`ResidualGaloisRep.exists_unipotent_model_V_of_isLocalRing_cartierDual`](thm.html#ResidualGaloisRep.exists_unipotent_model_V_of_isLocalRing_cartierDual), where the hypotheses available are finiteness, flatness and a bijection of the point set with a set of size $p^a$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    {M : Type} [Finite M] (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (a : ℕ) (hM : Nat.card M = p ^ a) :
    Module.Free ℤ_[p] H ∧ Module.finrank ℤ_[p] H = p ^ a := by sorry
