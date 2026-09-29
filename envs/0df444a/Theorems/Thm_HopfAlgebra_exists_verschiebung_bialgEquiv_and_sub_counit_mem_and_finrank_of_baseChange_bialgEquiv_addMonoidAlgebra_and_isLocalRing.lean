-- Prove2me | Theorems.Thm_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
-- name    : HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/43e44625-b647-5716-990c-f074ba70bd50
-- title:
--   Verschiebung, unit reduction, rank and local special fibre
-- statement:
--   Fix a prime $p$. Let $R$ be a local commutative domain equipped with an $R$-algebra structure on $\mathbb{Z}/p$ such that, for every $x \in R$, the structure map $R \to \mathbb{Z}/p$ kills $x$ exactly when $x$ lies in the maximal ideal of $R$. Let $A$ be a local commutative domain which is an $R$-algebra via a local homomorphism, flat and faithful as an $R$-module, whose residue field has characteristic $p$. Let $C$ be a commutative ring carrying a cocommutative Hopf algebra structure over $R$, free and finite as an $R$-module. Let $\Lambda$ be a finite abelian group with decidable equality and $\Lambda$ of cardinality $p^{n}$, and suppose given an $A$-bialgebra isomorphism $e : A \otimes_R C \cong A[\Lambda]$ onto the additive monoid algebra of $\Lambda$ over $A$. Then four assertions hold simultaneously: (1) there is a bialgebra automorphism $\mathrm{Ver}$ of $\mathbb{Z}/p \otimes_R C$ whose transpose on the Cartier dual, i.e. the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}(\mathbb{Z}/p \otimes_R C, \mathbb{Z}/p)$ with its dual bialgebra structure, sends every $\chi$ to $\chi^{p}$; (2) every $R$-algebra homomorphism $\chi : C \to A$ satisfies $\chi(c) - \mathrm{algebraMap}(\varepsilon(c)) \in \mathfrak{m}_A$ for all $c \in C$, where $\varepsilon$ is the counit of $C$; (3) $\operatorname{rank}_R C = |\Lambda|$; and (4) the ring $\kappa_A \otimes_R C$, with $\kappa_A$ the residue field of $A$, is local.
--
--   This is the statement that a finite flat commutative group scheme over a local base which becomes diagonalisable (the Cartier dual of a constant $p$-group $\Lambda$) after a faithfully flat local base change is of multiplicative type, expressed through four consequences: Verschiebung acting as $p$-th power on characters, reduction of every integral point to the identity, the expected rank, and an infinitesimal special fibre. It is used in the analysis of the finite part and toric closure of the Néron model of the modular Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    [FaithfulSMul R A] [CharP (IsLocalRing.ResidueField A) p]
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) :
    (∃ Ver : ZMod p ⊗[R] C ≃ₐc[ZMod p] ZMod p ⊗[R] C,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[R] C), CartierDual.map (Ver : ZMod p ⊗[R] C →ₐc[ZMod p] ZMod p ⊗[R] C) χ = χ ^ p) ∧
    (∀ (χ : C →ₐ[R] A) (c : C), χ c - algebraMap R A (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal A) ∧
    Module.finrank R C = Fintype.card Λ ∧

    IsLocalRing (IsLocalRing.ResidueField A ⊗[R] C) := by sorry
