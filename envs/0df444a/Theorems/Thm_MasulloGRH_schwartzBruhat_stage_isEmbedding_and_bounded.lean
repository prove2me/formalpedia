-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_stage_isEmbedding_and_bounded
-- name    : MasulloGRH.schwartzBruhat_stage_isEmbedding_and_bounded
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:58.952845+00:00
-- url     : https://prove2.me/theorems/758a1447-1afb-4154-ba89-ef25d4b36d9f
-- title:
--   Lemma D.1.5.6 — the stages $\mathcal S(k,\Gamma)\hookrightarrow\mathcal S(G)$ are topological embeddings and every bounded subset of $\mathcal S(G)$ is bounded in one stage
-- statement:
--   **Strictness and regularity of the inductive system defining $\mathcal S(G)$** (Lemma D.1.5.6).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Assume in addition that $G$ is **second countable**.
--
--   1. For every structural pair $(\Gamma,k)$ of $G$ and every identification $\Gamma/k\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$, the inclusion
--   $$\mathcal S(\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F)\cong\mathcal S(k,\Gamma)\hookrightarrow\mathcal S(G)$$
--   is a topological embedding: the topology induced on $\mathcal S(k,\Gamma)$ by $\mathcal S(G)$ is its intrinsic Fréchet topology.
--   2. For every bounded subset $B\subseteq\mathcal S(G)$ there is a structural pair $(\Gamma,k)$ such that $B$ is the image of a bounded subset of $\mathcal S(k,\Gamma)$.
--
--   For second countable $G$ the space $\mathcal S(G)$ is a strict inductive limit of a sequence of Fréchet spaces; the two assertions express the strictness and the regularity of this limit for all the concrete stages $\mathcal S(k,\Gamma)$. Both parts are used in the proof of the Main Structure Theorem D.1.5.7 (for instance for the Heine–Borel property of $\mathcal S(G)$), and part 2 (regularity of the inductive limit) is what controls the bounded sets entering the strong dual topology of the space $\mathcal S(G)'_\beta$ of tempered distributions.
--
--   **Formalization Note.** A stage is given by subgroups `Γ k`, numbers `m n r s`, orders `d : Fin s → ℕ` of the cyclic factors of $F$, a presentation `π : Γ →* Multiplicative (ElemGroup m n r s d)` (continuous, open, surjective, with kernel `k`, all `d i ≠ 0`) and the linear map `SchwartzBruhat.ofElem Γ k π hs hπ : ElemSchwartz m n r s d → SchwartzBruhat G` of the platform definition `MasulloGRH_SchwartzBruhat`. Part 1 says that this map is `Topology.IsEmbedding`; part 2 gives a von Neumann bounded set `B'` of `ElemSchwartz m n r s d` with `B = ofElem '' B'`. That $\mathcal S(G)$ is Hausdorff (also asserted in Lemma D.1.5.6(1)) is part of the platform theorem `MasulloGRH.schwartzBruhat_main_structure` and is not repeated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 763, Lemma D.1.5.6; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, 6.4 and 6.5

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_stage_isEmbedding_and_bounded
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π),
        IsEmbedding (SchwartzBruhat.ofElem Γ k π hs hπ)) ∧
    (∀ B : Set (SchwartzBruhat G), Bornology.IsVonNBounded ℂ B →
      ∃ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (B' : Set (ElemSchwartz m n r s d)),
        Bornology.IsVonNBounded ℂ B' ∧ B = SchwartzBruhat.ofElem Γ k π hs hπ '' B') := by sorry

end MasulloGRH
