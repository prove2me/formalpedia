-- Prove2me | Theorems.Thm_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
-- name    : HopfAlgebra.finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/6c0b2ec8-9b84-5738-ac93-bff6f9867297
-- title:
--   Tangent–cotangent duality with operators for finite Hopf algebras
-- statement:
--   Let $k$ be a field and $B$ a commutative ring carrying a Hopf algebra structure over $k$ whose comultiplication is cocommutative and which is finite as a $k$-module. Let $\iota$ be a type and $\psi : \iota \to (B \to_{\mathrm{ac}[k]} B)$ a family of bialgebra endomorphisms of $B$. Write $B^{D} = \mathrm{CartierDual}\,k\,B$, the $k$-linear dual $\mathrm{Hom}_k(B,k)$ with its Cartier-dual ring and bialgebra structure, and $I = \ker(\varepsilon_{B^{D}})$ for the kernel of the counit, viewed as an algebra map; for each $i$ let $\psi_i^{D} : B^{D} \to B^{D}$ be the transposed bialgebra endomorphism [`CartierDual.map (ψ i)`](def/HopfAlgebra_CartierDualMap.html#L102), regarded as a $k$-algebra map. Assume for every $i$ that $I$ is contained in the preimage of $I$ under $\psi_i^{D}$, i.e. $\psi_i^{D}(I) \subseteq I$. Let $P = \mathrm{primitives}\,k\,B$ be the kernel of the $k$-linear map $x \mapsto \Delta x - x \otimes 1 - 1 \otimes x$. Then the $k$-dimension of the quotient of $P$ by the supremum over $i$ of the submodules $\psi_i(P) \cap P$ (the images $\psi_i(P)$ pulled back along the inclusion of $P$) equals the $k$-dimension of the intersection over $i$ of the kernels of the induced maps $I/I^{2} \to I/I^{2}$ obtained from $\psi_i^{D}$ via `Ideal.mapCotangent`.
--
--   This is the functorial form of the tangent–cotangent duality between the primitives of a finite commutative cocommutative Hopf algebra and the cotangent space of its Cartier dual, here recorded as an equality of dimensions compatible with a family of bialgebra operators and their transposes. It is used in the computation of the cardinality of a Dieudonné module modulo the images of Verschiebung and of a Hecke operator, matched against torsion in a quotient of the integral lattice attached to a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual.lean

import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
    (k : Type) [Field k] (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Module.Finite k B] {ι : Type} (ψ : ι → (B →ₐc[k] B))
    (hI : ∀ i, RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)) ≤
      (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B))).comap
        (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B)) :
    Module.finrank k (↥(primitives k B) ⧸
        ⨆ i, ((primitives k B).map (ψ i).toLinearMap).comap (primitives k B).subtype)
      = Module.finrank k ↥(⨅ i, LinearMap.ker
          (Ideal.mapCotangent (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i))) := by sorry
