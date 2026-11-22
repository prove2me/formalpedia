-- Prove2me | Theorems.Thm_MasulloGRH_epsTensor_map_isEmbedding
-- name    : MasulloGRH.epsTensor_map_isEmbedding
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:28.954722+00:00
-- url     : https://prove2.me/theorems/38b50a4c-9902-4a03-9ef6-e592c53cbea7
-- title:
--   The injective tensor product $T_1\otimes_\varepsilon T_2$ of linear topological embeddings is a topological embedding
-- statement:
--   **The injective tensor product respects subspaces.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E_1,E_2,F_1,F_2$ be Hausdorff locally convex spaces and let $T_1:E_1\to F_1$, $T_2:E_2\to F_2$ be continuous linear maps which are **topological embeddings** (injective, and homeomorphisms onto their images). Then
--   $$T_1\otimes_\varepsilon T_2:\ E_1\otimes_\varepsilon E_2\longrightarrow F_1\otimes_\varepsilon F_2,\qquad x_1\otimes x_2\mapsto T_1x_1\otimes T_2x_2,$$
--   is a topological embedding.
--
--   This is the property that gives the injective tensor product its name. In the paper it yields strictness of the inductive systems $E_i\widehat\otimes_\varepsilon F_j$ (Proposition C.2.3.13) and, together with nuclearity ($\otimes_\pi=\otimes_\varepsilon$), the good behaviour of $\widehat\otimes_\pi$ under subspace inclusions (Proposition C.2.3.14).
--
--   **Deviation from the source.** Only the statement for the uncompleted tensor products is given (the source also asserts it for the extension $T_1\widehat\otimes_\varepsilon T_2$ to the completions and for isometric embeddings of normed spaces). The sentence on p. 679 of the source claiming the analogue of this lemma for projective tensor products is false ($\otimes_\pi$ does not respect subspaces) and has no counterpart here.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. $T_1\otimes T_2$ is `TensorProduct.map T₁.toLinearMap T₂.toLinearMap`, and the conclusion is `Topology.IsEmbedding` between `epsTensorTopology E₁ E₂` and `epsTensorTopology F₁ F₂`. $E_1,E_2$ share a universe and $F_1,F_2$ share a universe.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 678, Lemma C.2.3.5(1); classical reference: F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 43.7

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem epsTensor_map_isEmbedding (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : Topology.IsEmbedding T₁) (h₂ : Topology.IsEmbedding T₂) :
    @Topology.IsEmbedding (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (epsTensorTopology E₁ E₂)
      (epsTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by sorry

end MasulloGRH
