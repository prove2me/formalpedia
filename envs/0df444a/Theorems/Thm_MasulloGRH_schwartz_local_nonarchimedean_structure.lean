-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_local_nonarchimedean_structure
-- name    : MasulloGRH.schwartz_local_nonarchimedean_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:46:48.395329+00:00
-- url     : https://prove2.me/theorems/8475d204-6a58-4880-9ce8-6fe931f6e0e2
-- title:
--   Proposition 2.1.2.4 — structure of $\mathcal S(F_v)$ at a finite place
-- statement:
--   Let $F$ be a number field, $v$ a finite place, $F_v$ the completion and $\mathcal S(F_v)$ the Schwartz–Bruhat space of the additive group $F_v$, i.e. the space of locally constant complex functions with compact support on $F_v$, with its inductive limit topology.
--
--   1. $\mathcal S(F_v)$ has countable dimension over $\mathbb C$, it carries the finest locally convex topology, and it is a strict LF-space.
--   2. $\mathcal S(F_v)$ is a Hausdorff locally convex space that is complete, nuclear and Montel, and its strong dual $\mathcal S(F_v)'_\beta$ is a nuclear Fréchet space.
--   3. Every linear subspace $V\subset\mathcal S(F_v)$ is linearly and topologically complemented: there is a subspace $W$ with $V\oplus W=\mathcal S(F_v)$ algebraically such that the sum map $V\times W\to\mathcal S(F_v)$ is a homeomorphism.
--
--   At the finite places the Schwartz–Bruhat spaces are countable-dimensional spaces with the finest locally convex topology, so that every linear map out of them is continuous.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.1.2, Proposition 2.1.2.4, p. 64

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem schwartz_local_nonarchimedean_structure (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.rank ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ≤ Cardinal.aleph0 ∧
      HasFinestLocallyConvexTopology (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsStrictLF (SchwartzBruhat (Multiplicative (v.adicCompletion F)))) ∧
    (IsHLCS (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsCompleteTVS (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsNuclear (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsMontel (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsFrechet (StrongDual ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F)))) ∧
      IsNuclear (StrongDual ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))))) ∧
    (∀ V : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))),
      ∃ W : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))), IsCompl V W ∧
        Continuous (fun p : V × W =>
          ((p.1 : SchwartzBruhat (Multiplicative (v.adicCompletion F))) + p.2)) ∧
        IsOpenMap (fun p : V × W =>
          ((p.1 : SchwartzBruhat (Multiplicative (v.adicCompletion F))) + p.2))) := by sorry

end MasulloGRH
