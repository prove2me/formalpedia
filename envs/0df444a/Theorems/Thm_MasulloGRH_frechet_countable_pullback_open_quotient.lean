-- Prove2me | Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient
-- name    : MasulloGRH.frechet_countable_pullback_open_quotient
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T22:41:20.776422+00:00
-- url     : https://prove2.me/theorems/a549e418-5851-4ae3-8f6c-2d8b5f46ca6c
-- title:
--   Open Fréchet pullback projection for a countable covering
-- statement:
--   Let $A$ and each $B_n$ be complex Fréchet spaces, and let $G$ be a complex vector space with a Hausdorff topology. Suppose $a:A\to G$ and $b_n:B_n\to G$ are continuous linear maps and the ranges of the $b_n$ cover $G$. For some $n$, the first projection from the closed pullback
--
--   $$P_n=\{(x,y)\in A\times B_n:a(x)=b_n(y)\}\longrightarrow A$$
--
--   is continuous, open, and surjective, with $P_n$ given the subspace topology. The maps $b_n$ may have kernels. The conclusion supplies a quotient presentation of a Fréchet test space using a single stage of the cover.
--
--   Each $P_n$ is a closed subspace of a product of Fréchet spaces. Baire category applied to the covering of $A$ selects a projection with nonmeagre range. For any zero-neighborhood $V$ in its domain, the range is a countable union of dilates of the image of $V$. Thus the closure of that image has nonempty interior. Taking differences gives the closed-image neighborhood condition used in the Fréchet open mapping argument. Completeness then removes the closures and yields an open surjection.
-- source:
--   A. M. Masullo, The Music of the Primes, 20 November 2026 draft, Appendix C, Lemma C.1.5.4, p. 665, using its closed pullback construction and the proof of Theorem C.1.5.5, pp. 665–666. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Topology

theorem MasulloGRH.frechet_countable_pullback_open_quotient
    (A : Type*) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] (hA : IsFrechet A)
    (B : ℕ → Type*) [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
    [∀ n, TopologicalSpace (B n)] (hB : ∀ n, IsFrechet (B n))
    (G : Type*) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [T2Space G]
    (a : A →ₗ[ℂ] G) (ha : Continuous a) (b : ∀ n, B n →ₗ[ℂ] G)
    (hb : ∀ n, Continuous (b n)) (hcover : ∀ g : G, ∃ n, g ∈ Set.range (b n)) :
    ∃ n, IsOpenQuotientMap
      (fun z : {p : A × B n // a p.1 = b n p.2} => z.val.1) := by sorry
