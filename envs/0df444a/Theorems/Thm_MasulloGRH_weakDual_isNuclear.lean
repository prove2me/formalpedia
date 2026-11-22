-- Prove2me | Theorems.Thm_MasulloGRH_weakDual_isNuclear
-- name    : MasulloGRH.weakDual_isNuclear
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:28.611732+00:00
-- url     : https://prove2.me/theorems/768d60b0-c606-49eb-888a-b77823a51c0e
-- title:
--   The weak dual $E'_\sigma$ of a Hausdorff locally convex space is nuclear
-- statement:
--   **Weak duals are nuclear.**
--
--   All vector spaces are over $\mathbb C$. A Hausdorff locally convex space $N$ is **nuclear** if for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on $N\otimes F$ coincide, i.e. the identity $N\otimes_\pi F\to N\otimes_\varepsilon F$ is a linear topological isomorphism.
--
--   Let $E$ be a Hausdorff locally convex space and let $E'_\sigma$ be its **weak dual**: the space $E'$ of continuous linear functionals on $E$ with the weak-$*$ topology $\sigma(E',E)$ of pointwise convergence on $E$. Then
--   $$E'_\sigma\ \text{ is nuclear.}$$
--
--   In the source this is deduced from the fact that every local Banach space $\widehat{(E'_\sigma)}_U$ of the weak dual is finite-dimensional (each continuous seminorm on $E'_\sigma$ vanishes on a subspace of finite codimension). Weak duals are the basic examples of nuclear spaces that are in general neither metrizable nor complete; the lemma is used in Remark C.2.4.7 for $C(K)'_\sigma$.
--
--   **Formalization Note.** $E'_\sigma$ is Mathlib's `WeakDual ℂ E`; `IsNuclear` is the platform definition of `Def_MasulloGRH_LocallyConvex` (it includes that the space is Hausdorff locally convex, and quantifies over spaces $F$ in the same universe). Only the nuclearity assertion of the lemma is stated, not the finite-dimensionality of the local Banach spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 687, Lemma C.2.4.4

import Definitions.Def_MasulloGRH_LocallyConvex

open Topology
set_option autoImplicit false
universe u

namespace MasulloGRH

theorem weakDual_isNuclear (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) : IsNuclear (WeakDual ℂ E) := by sorry

end MasulloGRH
