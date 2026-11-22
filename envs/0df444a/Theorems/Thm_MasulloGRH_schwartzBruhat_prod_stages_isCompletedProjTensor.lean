-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor
-- name    : MasulloGRH.schwartzBruhat_prod_stages_isCompletedProjTensor
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T18:25:39.742614+00:00
-- url     : https://prove2.me/theorems/d68a285e-f8c8-45d2-93ed-b286e2a309f7
-- title:
--   Product stages: $\mathcal S(G_1\times G_2)$ is the strict inductive limit of completed projective tensor products of stages of $\mathcal S(G_1)$, $\mathcal S(G_2)$
-- statement:
--   **Product stages of $\mathcal S(G_1\times G_2)$** (auxiliary lemma for the proof of Lemma D.1.8.1(1)): the Schwartz–Bruhat space of a product of two second countable locally compact abelian groups is the strict inductive limit of completed projective tensor products of stages of the Schwartz–Bruhat spaces of the factors.
--
--   Let $G_1$, $G_2$ be second countable Hausdorff locally compact abelian groups (written multiplicatively) and let $\mathcal S(G_1)$, $\mathcal S(G_2)$, $\mathcal S(G_1\times G_2)$ be their Schwartz–Bruhat spaces (Definition D.1.5.3: the union of the stages $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ over the structural pairs $(\Gamma,k)$, with the locally convex inductive limit topology (D.1.5.4)).
--
--   **Statement.** There are increasing sequences of linear subspaces $E_n\subseteq\mathcal S(G_1)$, $F_n\subseteq\mathcal S(G_2)$ and $Y_n\subseteq\mathcal S(G_1\times G_2)$ $(n\in\mathbb N)$, each endowed with the topology induced by the ambient space, such that:
--   1. $\bigcup_n E_n=\mathcal S(G_1)$, $\bigcup_n F_n=\mathcal S(G_2)$ and $\bigcup_n Y_n=\mathcal S(G_1\times G_2)$;
--   2. every $E_n$ and every $F_n$ is a Fréchet space;
--   3. each of the three spaces carries the locally convex inductive limit topology of its sequence: the topology of $\mathcal S(G_1)$ is the finest locally convex topology on $\mathcal S(G_1)$ for which all inclusions $E_n\hookrightarrow\mathcal S(G_1)$ are continuous, and likewise for $\mathcal S(G_2)$ with the $F_n$ and for $\mathcal S(G_1\times G_2)$ with the $Y_n$;
--   4. for every $n$ there is a linear map $j_n\colon E_n\otimes F_n\to Y_n$ with
--   $$j_n(f\otimes g)(x_1,x_2)=f(x_1)\,g(x_2)\qquad(f\in E_n,\ g\in F_n,\ (x_1,x_2)\in G_1\times G_2),$$
--   here $f\otimes g\in E_n\otimes F_n$ is the algebraic tensor product of $f$ and $g$, such that $(Y_n,j_n)$ is a completed projective tensor product $E_n\,\widehat\otimes_\pi\,F_n$: $Y_n$ is a complete Hausdorff locally convex space, $j_n$ is injective with dense range, and the projective tensor topology of $E_n\otimes_\pi F_n$ is the topology induced by $j_n$.
--
--   Classically one takes $E_n=\mathcal S(k_{1,n},\Gamma_{1,n})$ and $F_n=\mathcal S(k_{2,n},\Gamma_{2,n})$ for cofinal increasing sequences of structural pairs of $G_1$ and of $G_2$ (they exist because the groups are second countable), and $Y_n=\mathcal S(k_{1,n}\times k_{2,n},\ \Gamma_{1,n}\times\Gamma_{2,n})$. The product pairs are structural pairs of $G_1\times G_2$ and are cofinal among all structural pairs of $G_1\times G_2$; the quotient $(\Gamma_{1,n}\times\Gamma_{2,n})/(k_{1,n}\times k_{2,n})$ is the product of the elementary abelian Lie groups $\Gamma_{i,n}/k_{i,n}\cong\mathbb R^{a_{i,n}}\times\mathbb T^{b_{i,n}}\times\mathbb Z^{c_{i,n}}\times\Phi_{i,n}$ ($i=1,2$, $\Phi_{i,n}$ a finite abelian group), and item 4 is the kernel theorem $\mathcal S(A_1)\,\widehat\otimes_\pi\,\mathcal S(A_2)\cong\mathcal S(A_1\times A_2)$ for elementary abelian Lie groups $A_1$, $A_2$ (the spaces are nuclear Fréchet spaces). The lemma is the stage-by-stage part of the proof of Lemma D.1.8.1(1): together with the facts that the inductive tensor product commutes with locally convex inductive limits and coincides with the projective one on Fréchet spaces, it gives the kernel theorem $\mathcal S(G_1)\,\overline\otimes\,\mathcal S(G_2)\cong\mathcal S(G_1\times G_2)$ for the completed inductive tensor product.
--
--   **Formalization Note.** The spaces and their topologies are those of the platform definition `MasulloGRH_SchwartzBruhat`; `IsFrechet` and the inductive-limit description of item 3 are as in `MasulloGRH_LocallyConvex` (the same form as `IsStrictLF`), and item 4 uses the predicate `IsCompletedProjTensor` of `TopologicalTensorProduct_Completion`. The steps are `Submodule`s with the subspace topology. Both groups live in one universe because `IsCompletedProjTensor` is stated for two spaces in one universe.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 778, Lemma D.1.8.1(1), eq. (D.1.8.1); auxiliary lemma for the proof of Lemma D.1.8.1(1) (MasulloGRH.schwartzBruhat_prod_isCompletedIndTensor): the stage-level kernel theorem on cofinal product structural pairs

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_TopologicalTensorProduct_Completion

open TensorProduct Topology

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_prod_stages_isCompletedProjTensor
    (G₁ G₂ : Type u) [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] :
    ∃ (X₁ : ℕ → Submodule ℂ (SchwartzBruhat G₁)) (X₂ : ℕ → Submodule ℂ (SchwartzBruhat G₂))
      (Y : ℕ → Submodule ℂ (SchwartzBruhat (G₁ × G₂))),
      Monotone X₁ ∧ Monotone X₂ ∧ Monotone Y ∧
      (∀ f, ∃ n, f ∈ X₁ n) ∧ (∀ g, ∃ n, g ∈ X₂ n) ∧ (∀ h, ∃ n, h ∈ Y n) ∧
      (∀ n, IsFrechet (X₁ n)) ∧ (∀ n, IsFrechet (X₂ n)) ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat G₁)) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat G₁) t ∧
          ∀ n, @Continuous (X₁ n) (SchwartzBruhat G₁) _ t Subtype.val} ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat G₂)) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat G₂) t ∧
          ∀ n, @Continuous (X₂ n) (SchwartzBruhat G₂) _ t Subtype.val} ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat (G₁ × G₂))) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat (G₁ × G₂)) t ∧
          ∀ n, @Continuous (Y n) (SchwartzBruhat (G₁ × G₂)) _ t Subtype.val} ∧
      ∀ n, ∃ jn : X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] Y n,
        (∀ (f : X₁ n) (g : X₂ n) (p : G₁ × G₂),
          ((jn (f ⊗ₜ[ℂ] g) : SchwartzBruhat (G₁ × G₂)) : G₁ × G₂ → ℂ) p =
            (f : SchwartzBruhat G₁) p.1 * (g : SchwartzBruhat G₂) p.2) ∧
        IsCompletedProjTensor (X₁ n) (X₂ n) jn := by sorry

end MasulloGRH
