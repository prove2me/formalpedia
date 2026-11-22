-- Prove2me | Theorems.Thm_MasulloGRH_indTensor_eq_final_of_final
-- name    : MasulloGRH.indTensor_eq_final_of_final
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:30.136978+00:00
-- url     : https://prove2.me/theorems/a5e0f9db-ee4f-4b08-929e-80ca6c7caed7
-- title:
--   The inductive tensor product commutes with locally convex inductive limits: $\varinjlim_{(i,j)}E_i\otimes_\iota F_j\simeq E\otimes_\iota F$
-- statement:
--   **Inductive tensor products commute with locally convex inductive limits.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $(E_i)_{i\in I}$ and $(F_j)_{j\in J}$ be families of Hausdorff locally convex spaces, and let $E$, $F$ be Hausdorff locally convex spaces which are their locally convex inductive limits: there are linear maps $a_i:E_i\to E$ and $b_j:F_j\to F$ whose images span $E$, resp. $F$, and $E$ (resp. $F$) carries the finest locally convex topology for which all $a_i$ (resp. all $b_j$) are continuous. Then $E\otimes_\iota F$ is the locally convex inductive limit of the spaces $E_i\otimes_\iota F_j$: the inductive topology of $E\otimes F$ is the finest locally convex topology for which all the maps
--   $$a_i\otimes b_j:\ E_i\otimes_\iota F_j\longrightarrow E\otimes F,\qquad (i,j)\in I\times J,$$
--   are continuous. Equivalently, the canonical continuous linear map
--   $$\varinjlim_{(i,j)\in I\times J}E_i\otimes_\iota F_j\longrightarrow E\otimes_\iota F$$
--   is a linear topological isomorphism.
--
--   This is the reason for using the inductive tensor product on LF-spaces (the corresponding statement for $\otimes_\pi$ fails in general); it is one of the most frequently used facts of Appendix C in the main text, e.g. for $\mathcal S(G_1)\,\overline\otimes\,\mathcal S(G_2)$ with $\mathcal S(G_k)$ inductive limits of Fréchet spaces.
--
--   **Deviation from the source.** Only the assertion (C.2.3.26) about the uncompleted tensor products is stated. The further assertions of Proposition C.2.3.13(2) about the limit of the *completed* stages $E_i\,\overline\otimes\,F_j$, (C.2.3.27), are not included (as printed, the map (C.2.3.27) need not be injective in general).
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. As elsewhere on the platform, a locally convex inductive limit is encoded by its universal topology: `htopE` says that the topology of $E$ is `sInf {t | t locally convex ∧ ∀ i, a i continuous into t}` (the finest such topology), and `ha : ⨆ i, LinearMap.range (a i) = ⊤` says that the images span $E$. For a directed system $E=\varinjlim E_i$ with its canonical maps both hold, and $E\otimes F$ with the maps $a_i\otimes b_j$ is the algebraic inductive limit of the $E_i\otimes F_j$; the transition maps of the systems are not needed to state the result, so the families are arbitrary (the source takes filtered index sets). The stage spaces share a universe, which may differ from that of $E$, $F$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 683, Proposition C.2.3.13(2), (C.2.3.26); classical reference: A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Memoirs of the AMS No. 16, Ch. I, §3, No. 1, Prop. 14, p. 76

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem indTensor_eq_final_of_final (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {I J : Type*} (X : I → Type v) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)]
    (Y : J → Type v) [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)]
    [∀ j, TopologicalSpace (Y j)]
    (hX : ∀ i, IsHLCS (X i)) (hY : ∀ j, IsHLCS (Y j)) (hE : IsHLCS E) (hF : IsHLCS F)
    (a : ∀ i, X i →ₗ[ℂ] E) (b : ∀ j, Y j →ₗ[ℂ] F)
    (ha : ⨆ i, LinearMap.range (a i) = ⊤) (hb : ⨆ j, LinearMap.range (b j) = ⊤)
    (htopE : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ i, @Continuous (X i) E _ t (a i)})
    (htopF : ‹TopologicalSpace F› =
      sInf {t | IsLocallyConvexTopology F t ∧ ∀ j, @Continuous (Y j) F _ t (b j)}) :
    indTensorTopology E F =
      sInf {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧ ∀ i j,
        @Continuous (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) (indTensorTopology (X i) (Y j)) t
          (TensorProduct.map (a i) (b j))} := by sorry

end MasulloGRH
