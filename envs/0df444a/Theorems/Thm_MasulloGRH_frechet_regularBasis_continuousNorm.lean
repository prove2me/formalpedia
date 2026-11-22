-- Prove2me | Theorems.Thm_MasulloGRH_frechet_regularBasis_continuousNorm
-- name    : MasulloGRH.frechet_regularBasis_continuousNorm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:08.164274+00:00
-- url     : https://prove2.me/theorems/3d92470f-7b33-40c4-9c95-052c737bd540
-- title:
--   Remark 4.1.2.3 (Kalton) — a Fréchet space with a regular Schauder basis has a continuous norm and no complemented subspace isomorphic to $\mathbb C^{\mathbb N}$
-- statement:
--   **Remark 4.1.2.3 (Kalton) — regular Schauder bases and continuous norms.** Let $E$ be a complex Fréchet space and $(x_m)_{m\ge0}$ a Schauder basis of $E$ with coefficient functionals $(f_m)_{m\ge0}\subset E'$. Assume the basis is *regular* (Definition 4.1.2.1(6)): there is a $0$-neighbourhood $U$ in $E$ with $x_m\notin U$ for all $m\ge0$. Then
--
--   1. $E$ has a continuous norm, i.e. a continuous seminorm $q$ on $E$ such that $q(u)=0$ implies $u=0$;
--   2. $E$ has no complemented closed subspace that is linearly and topologically isomorphic to $\prod_{m\in\mathbb N}\mathbb C=\mathbb C^{\mathbb N}$ (with the product topology).
--
--   The paper uses this observation as a sanity check for the Schauder bases it constructs on nuclear Fréchet subquotients of the strict LF-spaces $\mathcal S_I(G)$. For comparison, the coordinate space $\mathbb C^{\mathbb N}$ is a Fréchet space without a continuous norm, and its unit-vector basis is not regular.
--
--   **Formalization Note.** Regularity is the platform's `MasulloGRH.IsRegularBasis`, Schauder bases and Fréchet spaces are `MasulloGRH.IsSchauderBasis` and `MasulloGRH.IsFrechet`. A continuous norm is encoded as a continuous `Seminorm ℂ E` vanishing only at $0$. "Complemented" is Mathlib's `Submodule.ClosedComplemented` (existence of a continuous linear projection of $E$ onto the subspace), and $\mathbb C^{\mathbb N}$ is `ℕ → ℂ` with its product topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 159, Remark 4.1.2.3; classical reference: N. J. Kalton, Normalization properties of Schauder bases, Proc. London Math. Soc. (3) 22 (1971), 91–105, §2, Thm. 2.3, p. 93 (as cited by the paper)

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace MasulloGRH

theorem frechet_regularBasis_continuousNorm
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f)
    (hreg : IsRegularBasis x) :
    (∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u : E, q u = 0 → u = 0) ∧
      ¬ ∃ S : Submodule ℂ E, IsClosed (S : Set E) ∧ S.ClosedComplemented ∧
        Nonempty (S ≃L[ℂ] (ℕ → ℂ)) := by sorry

end MasulloGRH
