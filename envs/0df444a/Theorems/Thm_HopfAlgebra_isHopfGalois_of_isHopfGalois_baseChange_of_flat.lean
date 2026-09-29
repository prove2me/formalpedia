-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat
-- name    : HopfAlgebra.isHopfGalois_of_isHopfGalois_baseChange_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/fdbcc094-c3af-5d5e-bc26-5a23f602b89f
-- title:
--   Hopf–Galois descends from the generic fibre under flatness
-- statement:
--   Let $R$ be a commutative integral domain and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $H$ and $H'$ be commutative rings carrying Hopf $R$-algebra structures, with $H$ flat as an $R$-module, and let $qc : H \to H'$ be a homomorphism of $R$-bialgebras which is surjective as a function. Write $B =$ [`HopfAlgebra.hopfKer qc`](def/HopfAlgebra_HopfKer.html#L19) for the equaliser subalgebra $\{h \in H : (\mathrm{id}_H \otimes qc)(\Delta h) = h \otimes 1\}$ of $H$, and assume $H$ is flat as a $B$-module. Assume further that the base-changed $K$-bialgebra map $\mathrm{id}_K \otimes qc : K \otimes_R H \to K \otimes_R H'$ satisfies [`HopfAlgebra.IsHopfGalois`](def/HopfAlgebra_HopfKer.html#L66). Then [`HopfAlgebra.IsHopfGalois qc`](def/HopfAlgebra_HopfKer.html#L66) holds, that is: the $R$-linear canonical map `canMap qc` $: H \otimes_R H \to H \otimes_R H'$ is surjective, and every element of its kernel lies in the $R$-submodule spanned by the balancing relations $(a h) \otimes a' - a \otimes (h a')$ with $a, a' \in H$ and $h \in B$.
--
--   This is the flat-descent step for the torsor (Hopf–Galois) condition: a quotient of Hopf algebras which is a torsor generically, over a Hopf algebra flat over its coinvariants, is a torsor integrally. It serves as the passage from the generic fibre to the integral statement, and is used in [`HopfAlgebra.isHopfGalois_of_finitePartIdempotent`](thm.html#HopfAlgebra.isHopfGalois_of_finitePartIdempotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.isHopfGalois_of_isHopfGalois_baseChange_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    [Module.Flat ↥(HopfAlgebra.hopfKer qc) H]
    (hK : HopfAlgebra.IsHopfGalois
      (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H')) :
    HopfAlgebra.IsHopfGalois qc := by sorry
