-- Prove2me | Theorems.Thm_MasulloGRH_indTensor_eq_projTensor_of_isFrechet
-- name    : MasulloGRH.indTensor_eq_projTensor_of_isFrechet
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:19.41657+00:00
-- url     : https://prove2.me/theorems/49392712-97be-4ad6-b846-706ac82d4a89
-- title:
--   For Fréchet spaces $E$, $F$ the inductive and projective tensor topologies coincide: $E\otimes_\iota F=E\otimes_\pi F$
-- statement:
--   **Inductive and projective tensor products of Fréchet spaces coincide.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Fréchet spaces (complete metrizable locally convex spaces). Then the canonical continuous linear map (the identity of $E\otimes F$)
--   $$E\otimes_\iota F\longrightarrow E\otimes_\pi F$$
--   is a linear topological isomorphism, i.e. the inductive and the projective topology on $E\otimes F$ are equal. In particular the completions $E\,\overline\otimes\,F$ and $E\widehat\otimes_\pi F$ coincide.
--
--   This corollary is used throughout the paper to pass between $\overline\otimes$ and $\widehat\otimes_\pi$ on the Fréchet stages of LF-spaces of Schwartz–Bruhat functions.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. `IsFrechet E` means: locally convex, complete (Hausdorff, every Cauchy filter converges) and metrizable. The statement is the equality of topologies `indTensorTopology E F = projTensorTopology E F`; the assertion about completions is an immediate consequence and is not stated separately.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 682, Corollary C.2.3.12, (C.2.3.24)

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem indTensor_eq_projTensor_of_isFrechet (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsFrechet E) (hF : IsFrechet F) :
    indTensorTopology E F = projTensorTopology E F := by sorry

end MasulloGRH
