-- Prove2me | Theorems.Thm_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField
-- name    : HopfAlgebra.exists_wittOrthogonal_unipotent_splitting_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/4bdd2079-6743-5027-a47c-6550555ab454
-- title:
--   Witt-orthogonal and unipotent parts of a finite commutative Hopf algebra
-- statement:
--   Let $k$ be a perfect field of characteristic $p$ ($p$ a prime), and let $A$ be a commutative ring carrying a Hopf algebra structure over $k$ which is finite-dimensional as a $k$-module and whose comultiplication is cocommutative. The assertion is the existence of two further commutative rings $A^w$ and $A^u$, each a finite-dimensional cocommutative Hopf algebra over $k$, together with morphisms of $k$-bialgebras $\mu : A \to A^w$ and $\iota : A^u \to A$ such that: $\mu$ is surjective; $\iota$ is injective; the Hopf kernel of $\mu$, i.e. the subalgebra of those $a \in A$ with $(\mathrm{id}_A \otimes \mu)(\Delta a) = a \otimes 1$ in $A \otimes_k A^w$, coincides as a subset of $A$ with the image of $\iota$; the Cartier dual of $A^u$, namely the $k$-linear dual $\mathrm{Module.Dual}\,k\,A^u$ with its ring structure, is a local ring; and, finally, for every commutative ring $D$ equipped with a $k$-bialgebra structure and every surjective bialgebra map $\varphi : A \to D$ annihilating the kernel ideal of $\mu$ (that is, $\mu a = 0$ implies $\varphi a = 0$), and for every $m \in \mathbb{N}$, the group $\mathrm{Deformation.wittHom}\,k\,p\,m\,D$ — the additive subgroup of primitive elements $x$ of $\mathrm{TruncatedWittVector}\,p\,m\,D$, those with $\Delta_* x = (\mathrm{incl}_L)_* x + (\mathrm{incl}_R)_* x$ in truncated Witt vectors over $D \otimes_k D$ — is zero. No $D$ is required to be finite-dimensional or a Hopf algebra.
--
--   On the scheme side this is the splitting of a finite commutative group scheme over a perfect field into a unipotent part and a part all of whose closed subgroups admit no nonzero homomorphisms to the truncated Witt vector groups $W_m$; note that it is formulated here as an exact sequence $A^u \hookrightarrow A \twoheadrightarrow A^w$ with $A^u$ the Hopf kernel of $\mu$, rather than as a direct product decomposition. It supports the analysis of homomorphisms into truncated Witt vector groups, being used in [`HopfAlgebra.wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective`](thm.html#HopfAlgebra.wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.lean

import Mathlib
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.exists_wittOrthogonal_unipotent_splitting_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A] :
    ∃ (Aw : Type v) (_ : CommRing Aw) (_ : HopfAlgebra k Aw) (_ : Module.Finite k Aw)
      (_ : Coalgebra.IsCocomm k Aw)
      (Au : Type v) (_ : CommRing Au) (_ : HopfAlgebra k Au) (_ : Module.Finite k Au)
      (_ : Coalgebra.IsCocomm k Au)
      (μ : A →ₐc[k] Aw) (ι : Au →ₐc[k] A),
      Function.Surjective μ ∧ Function.Injective ι ∧
      (∀ a : A, a ∈ HopfAlgebra.hopfKer μ ↔ a ∈ Set.range ι) ∧
      IsLocalRing (CartierDual k Au) ∧
      (∀ (D : Type w) [CommRing D] [Bialgebra k D] (φ : A →ₐc[k] D), Function.Surjective φ →
        (∀ a : A, μ a = 0 → φ a = 0) →
          ∀ (m : ℕ) (y : Deformation.wittHom k p m D), y = 0) := by sorry
