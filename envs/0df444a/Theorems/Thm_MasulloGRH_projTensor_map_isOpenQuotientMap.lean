-- Prove2me | Theorems.Thm_MasulloGRH_projTensor_map_isOpenQuotientMap
-- name    : MasulloGRH.projTensor_map_isOpenQuotientMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:38.40108+00:00
-- url     : https://prove2.me/theorems/7059113a-48ca-4bb5-b510-9159b925f961
-- title:
--   The projective tensor product $T_1\otimes_\pi T_2$ of quotient maps is a quotient map
-- statement:
--   **The projective tensor product respects quotient maps.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E_1,E_2,F_1,F_2$ be Hausdorff locally convex spaces and let $T_1:E_1\to F_1$, $T_2:E_2\to F_2$ be **quotient maps**, i.e. continuous, open and surjective linear maps. Then
--   $$T_1\otimes_\pi T_2:\ E_1\otimes_\pi E_2\longrightarrow F_1\otimes_\pi F_2,\qquad x_1\otimes x_2\mapsto T_1x_1\otimes T_2x_2,$$
--   is a quotient map: it is continuous, open and surjective.
--
--   This is the good behaviour of $\otimes_\pi$ dual to the behaviour of $\otimes_\varepsilon$ under embeddings; it follows from the description (C.2.3.15) of the neighbourhoods of $0$ in a projective tensor product. The paper uses it to reduce statements about inductive limits to direct sums (proof of Proposition C.2.3.10).
--
--   **Deviation from the source.** Only the uncompleted statement is given. The analogue for the completions (Proposition C.2.3.7: $T_1\widehat\otimes_\pi T_2$ is a quotient map onto its image, surjective when $E_1$, $E_2$ are metrizable) is more subtle and is not part of this statement.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. A quotient map of topological vector spaces is expressed by Mathlib's `IsOpenQuotientMap` (surjective, continuous, open); for a linear map between topological vector spaces this is equivalent to being a topological quotient map.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 679, §C.2.3.2, the sentence preceding Proposition C.2.3.7

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem projTensor_map_isOpenQuotientMap (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : IsOpenQuotientMap T₁) (h₂ : IsOpenQuotientMap T₂) :
    @IsOpenQuotientMap (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (projTensorTopology E₁ E₂)
      (projTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by sorry

end MasulloGRH
