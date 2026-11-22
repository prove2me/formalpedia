-- Prove2me | Theorems.Thm_MasulloGRH_strictInductiveLimit_induced_eq_and_t2Space
-- name    : MasulloGRH.strictInductiveLimit_induced_eq_and_t2Space
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:50.814303+00:00
-- url     : https://prove2.me/theorems/5dcda633-97c6-4d10-a574-cd18bd1c9bd6
-- title:
--   Dieudonné–Schwartz: a strict countable locally convex inductive limit induces the given topology on every step, and is Hausdorff if the steps are
-- statement:
--   **Strict inductive limits induce the topology of each step (Dieudonné–Schwartz).** Let $E$ be a complex vector space which is the union of an increasing sequence of linear subspaces
--   $$E_0\subset E_1\subset E_2\subset\cdots,\qquad E=\bigcup_{n\ge 0}E_n,$$
--   and let each $E_n$ carry a locally convex vector space topology $\tau_n$ such that the sequence is *strict*: for every $n$ the topology induced by $\tau_{n+1}$ on $E_n$ is $\tau_n$. Let $\tau$ be the locally convex inductive limit topology on $E$, i.e. the finest locally convex topology on $E$ for which all inclusions $(E_n,\tau_n)\to E$ are continuous. Then:
--
--   1. $\tau$ induces $\tau_n$ on $E_n$ for every $n$; that is, every inclusion $(E_n,\tau_n)\to(E,\tau)$ is a topological embedding;
--   2. if every $\tau_n$ is Hausdorff, then $\tau$ is Hausdorff.
--
--   This is the basic theorem on strict inductive limits. The source invokes it each time it says that for a strict system the limit is automatically Hausdorff and every $E_n\to E$ is a topological embedding, for instance to pass from a strict sequence of Fréchet spaces to a strict LF-space in the sense of `MasulloGRH.IsStrictLF`, whose steps are subspaces carrying the induced topology.
--
--   **Formalization Note.** The steps are submodules `X n` of `E` with arbitrary topologies `τ n` on the subtypes, each assumed locally convex in the sense of `MasulloGRH.IsLocallyConvexTopology` (defined by a family of seminorms; no Hausdorff condition). The inductive limit topology is `sInf` of the set of locally convex topologies making all inclusions continuous; in Mathlib's order on topologies this infimum is the finest such topology (the same encoding as in `MasulloGRH.IsStrictLF` and `MasulloGRH.IsLF`). Part 1 needs no Hausdorff hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 662, Example C.1.4.6(4), and p. 664 (paragraph before Definition C.1.5.2); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, 6.4 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem strictInductiveLimit_induced_eq_and_t2Space (E : Type*) [AddCommGroup E] [Module ℂ E]
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (τ : ∀ n, TopologicalSpace (X n)) (hlc : ∀ n, IsLocallyConvexTopology (X n) (τ n))
    (hstrict : ∀ n, τ n =
      TopologicalSpace.induced (Submodule.inclusion (hmono (Nat.le_succ n))) (τ (n + 1))) :
    let t : TopologicalSpace E :=
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E (τ n) t Subtype.val}
    (∀ n, TopologicalSpace.induced (Subtype.val : X n → E) t = τ n) ∧
      ((∀ n, @T2Space (X n) (τ n)) → @T2Space E t) := by sorry

end MasulloGRH
