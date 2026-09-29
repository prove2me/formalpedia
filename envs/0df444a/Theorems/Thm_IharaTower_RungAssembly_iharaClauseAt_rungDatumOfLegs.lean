-- Prove2me | Theorems.Thm_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs
-- name    : IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/91eb0188-5044-59b5-aa0f-4de57f483579
-- title:
--   Ihara clause for an assembled rung datum
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, let $T$ and $T'$ be $\mathcal{O}$-algebras, and let $M$ be an $\mathcal{O}$-module and $T$-module with compatible scalars, and likewise $M'$ over $T'$; let $P$ and $P'$ be level pairings on $M$ and $M'$, that is, $\mathcal{O}$-bilinear forms $B$ with values in $\mathcal{O}$ that are bijective as maps $M \to \operatorname{Hom}_{\mathcal{O}}(M,\mathcal{O})$ and satisfy $B(tm,n)=B(m,tn)$. Fix $n \in \mathbb{N}$ and a leg datum $L$ of length $n$, consisting of families $\mathrm{iLeg}_k : M \to M'$, $\mathrm{jLeg}_k : M' \to M$ of $\mathcal{O}$-linear maps adjoint for $P$, $P'$ in each index, together with a table $\mathrm{table}_{k,k'} \in T$ with $\mathrm{jLeg}_k \circ \mathrm{iLeg}_{k'} = \mathrm{table}_{k,k'} \cdot \mathrm{id}$. Fix coefficients $c : \mathrm{Fin}\,n \to T$, an $\mathcal{O}$-algebra map $\mathrm{res} : T' \to T$, and an $\mathcal{O}$-algebra map $\pi_T : T \to \mathcal{O}$, and let $i = \sum_k \mathrm{iLeg}_k(c_k \cdot {-})$ be the assembled raising map of the rung datum `rungDatumOfLegs L c res`. Assume (i) $i(\mathrm{res}(t')m) = t' \, i(m)$ for all $t' \in T'$, $m \in M$, and (ii) every element of the $\mathcal{O}$-submodule of $M'$ annihilated by $\ker(\pi_T \circ \mathrm{res})$ is $i(m)$ for some $m \in M$ annihilated by $\ker \pi_T$. Then the Ihara clause holds for this rung datum at $\pi_T$ and $\pi_T \circ \mathrm{res}$: the image under $i$ of the submodule of $M$ annihilated by $\ker \pi_T$ equals the submodule of $M'$ annihilated by $\ker(\pi_T \circ \mathrm{res})$.
--
--   This is the abstract form of the Ihara-type surjectivity clause used in the level-change step: it records that the assembled degeneracy combination matches torsion submodules at corresponding points of the two Hecke algebras. It feeds the verification of the corner rung of the tower, [`IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung`](thm.html#IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs.lean

import Definitions.Def_HeckeModule_IharaRungDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaTower in

theorem IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs
    {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    {n : ℕ} (L : RungAssembly.LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) (πT : T →ₐ[𝒪] 𝒪)
    (hequiv : ∀ (t' : T') (m : M),
      (RungAssembly.rungDatumOfLegs L c res).i (res t' • m)
        = t' • (RungAssembly.rungDatumOfLegs L c res).i m)
    (hsurj : ∀ w' ∈ (Submodule.torsionBySet T' M'
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪,
      ∃ m ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪,
        (RungAssembly.rungDatumOfLegs L c res).i m = w') :
    IharaClauseAt (RungAssembly.rungDatumOfLegs L c res) πT (πT.comp res) := by sorry
