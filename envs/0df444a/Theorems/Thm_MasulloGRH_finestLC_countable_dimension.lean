-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_countable_dimension
-- name    : MasulloGRH.finestLC_countable_dimension
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:59:00.967391+00:00
-- url     : https://prove2.me/theorems/220851a4-3160-4e99-b788-2ba850ee001d
-- title:
--   Proposition C.2.5.1(6) — countable dimension: nuclear strict LF-space with nuclear Fréchet strong dual
-- statement:
--   Let $E$ be a complex vector space of **countable dimension**, equipped with its finest locally convex topology $\tau$. Then:
--
--   1. $(E,\tau)$ is a nuclear strict LF-space: it is the strict locally convex inductive limit of an increasing sequence of subspaces each of which is a nuclear Fréchet space (here even finite-dimensional);
--   2. $(E,\tau)$ is complete;
--   3. $(E,\tau)$ is nuclear;
--   4. $(E,\tau)$ is a Montel space;
--   5. the strong dual $E'_\beta$ is a Fréchet space;
--   6. the strong dual $E'_\beta$ is nuclear.
--
--   In the source this is the statement
--
--   $$\dim E\le\aleph_0\ \Longrightarrow\ (E,\tau)\ \text{is a nuclear strict LF-space; in particular it is complete, nuclear and Montel, and } E'_\beta \text{ is a nuclear Fréchet space.}$$
--
--   It applies to spaces such as $C_c^\infty(F_v)$ at a finite place $v$ and to the Schwartz–Bruhat spaces of finite adeles, which are countable-dimensional and carry the finest locally convex topology.
--
--   **Formalization Note.** Countable dimension is expressed as the existence of a countable subset spanning $E$. The six conclusions use the mission predicates `IsStrictLFOfNuclearFrechet`, `IsCompleteTVS`, `IsNuclear`, `IsMontel` (Hausdorff locally convex, closed bounded sets compact, reflexive) and `IsFrechet`; the strong dual is Mathlib's `StrongDual ℂ E` with the topology of uniform convergence on bounded sets.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(6), p. 692.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem finestLC_countable_dimension (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E)
    (hc : ∃ s : Set E, s.Countable ∧ Submodule.span ℂ s = ⊤) :
    IsStrictLFOfNuclearFrechet E ∧ IsCompleteTVS E ∧ IsNuclear E ∧ IsMontel E ∧
      IsFrechet (StrongDual ℂ E) ∧ IsNuclear (StrongDual ℂ E) := by sorry

end MasulloGRH
