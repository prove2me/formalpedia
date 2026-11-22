-- Prove2me | Theorems.Thm_MasulloGRH_epsTensor_map_denseRange
-- name    : MasulloGRH.epsTensor_map_denseRange
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:25.82462+00:00
-- url     : https://prove2.me/theorems/68b60f70-4680-4ea0-afa3-d4dd161dadb4
-- title:
--   The injective tensor product of linear topological embeddings with dense range has dense range
-- statement:
--   **Injective tensor products of dense embeddings are dense.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E_1,E_2,F_1,F_2$ be Hausdorff locally convex spaces and let $T_1:E_1\to F_1$, $T_2:E_2\to F_2$ be continuous linear maps which are topological embeddings with dense range. Then the image of
--   $$T_1\otimes_\varepsilon T_2:\ E_1\otimes_\varepsilon E_2\longrightarrow F_1\otimes_\varepsilon F_2$$
--   is dense in $F_1\otimes_\varepsilon F_2$.
--
--   Together with the embedding property (Lemma C.2.3.5(1)) this says that $T_1\otimes_\varepsilon T_2$ is again a topological embedding with dense range; applied to the inclusions $E_k\to\widehat E_k$ into the completions it shows that the completed injective tensor product does not change when the factors are replaced by their completions, $E_1\widehat\otimes_\varepsilon E_2\simeq\widehat E_1\widehat\otimes_\varepsilon\widehat E_2$ (C.2.3.11).
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. The conclusion is `DenseRange` of `TensorProduct.map T₁.toLinearMap T₂.toLinearMap` for the topology `epsTensorTopology F₁ F₂`. The hypotheses are those of the source; the embedding property of the tensor map is the separate statement Lemma C.2.3.5(1).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 678, Lemma C.2.3.5(2), first assertion

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem epsTensor_map_denseRange (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : Topology.IsEmbedding T₁) (h₂ : Topology.IsEmbedding T₂)
    (d₁ : DenseRange T₁) (d₂ : DenseRange T₂) :
    @DenseRange (F₁ ⊗[ℂ] F₂) (epsTensorTopology F₁ F₂) (E₁ ⊗[ℂ] E₂)
      (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by sorry

end MasulloGRH
