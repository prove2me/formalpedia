-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_prod_isCompletedIndTensor
-- name    : MasulloGRH.schwartzBruhat_prod_isCompletedIndTensor
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:23:18.349085+00:00
-- url     : https://prove2.me/theorems/8cfede8b-c915-40e7-8203-71ea231d3611
-- title:
--   Lemma D.1.8.1(1) — kernel theorem for Schwartz–Bruhat spaces: $\mathcal S(G_1)\,\overline\otimes\,\mathcal S(G_2)\simeq\mathcal S(G_1\times G_2)$ (completed inductive tensor product)
-- statement:
--   **The kernel theorem for Schwartz–Bruhat spaces** (Lemma D.1.8.1(1)).
--
--   Let $G_1$ and $G_2$ be **second countable** Hausdorff locally compact abelian groups, and let $\mathcal S(G_1)$, $\mathcal S(G_2)$, $\mathcal S(G_1\times G_2)$ be their Schwartz–Bruhat spaces (Bruhat's spaces: the union of the Fréchet spaces $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ over all structural pairs $(\Gamma,k)$, with the locally convex inductive limit topology; for second countable groups these are complete nuclear strict LF-spaces). For Hausdorff locally convex spaces $E$, $F$ the **inductive tensor product** $E\otimes_\iota F$ is the algebraic tensor product with the finest locally convex topology for which the canonical bilinear map $E\times F\to E\otimes F$ is separately continuous, and $E\,\overline\otimes\,F$ denotes its completion.
--
--   **Statement.** The canonical linear map
--   $$j\colon\mathcal S(G_1)\otimes\mathcal S(G_2)\longrightarrow\mathcal S(G_1\times G_2),\qquad j(f\otimes g)(x_1,x_2)=f(x_1)\,g(x_2),$$
--   is well defined, injective, a topological embedding for the inductive tensor product topology on the source, and has dense image in the complete space $\mathcal S(G_1\times G_2)$. Hence it extends to a linear topological isomorphism
--   $$\mathcal S(G_1)\,\overline\otimes\,\mathcal S(G_2)\ \xrightarrow{\ \sim\ }\ \mathcal S(G_1\times G_2).$$
--
--   For elementary abelian Lie groups the spaces are Fréchet, the inductive and projective tensor topologies coincide, and the statement is the classical $\mathcal S(\mathbb R^m)\widehat\otimes_\pi\mathcal S(\mathbb R^n)\simeq\mathcal S(\mathbb R^{m+n})$ and its analogues for tori and lattices. In general the inductive topology is the appropriate one: for LF-spaces the bilinear map $(f,g)\mapsto f\otimes g$ is separately continuous but need not be jointly continuous, so the projective tensor topology can be strictly coarser. The source uses the lemma to describe tempered distributions on product groups (Lemma D.1.8.1(2)).
--
--   **Formalization Note.** "The" completed tensor product is expressed by the platform predicate `MasulloGRH.IsCompletedIndTensor E F j` of `TopologicalTensorProduct_Completion`: the target of `j : E ⊗[ℂ] F →ₗ[ℂ] Y` is a complete Hausdorff locally convex space, `j` is injective with dense range, and the inductive tensor topology `indTensorTopology E F` equals the topology induced by `j`. Any two such completions are canonically isomorphic. The statement asserts the existence of such a `j` with `j (f ⊗ₜ g) p = f p.1 * g p.2`. The two groups live in the same universe because `indTensorTopology` is defined for two spaces in one universe.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 778, Lemma D.1.8.1(1), eq. (D.1.8.1)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_TopologicalTensorProduct_Completion

open TensorProduct Topology

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_prod_isCompletedIndTensor
    (G₁ G₂ : Type u) [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] :
    ∃ j : SchwartzBruhat G₁ ⊗[ℂ] SchwartzBruhat G₂ →ₗ[ℂ] SchwartzBruhat (G₁ × G₂),
      (∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂) (p : G₁ × G₂),
        j (f ⊗ₜ[ℂ] g) p = f p.1 * g p.2) ∧
      IsCompletedIndTensor (SchwartzBruhat G₁) (SchwartzBruhat G₂) j := by sorry

end MasulloGRH
