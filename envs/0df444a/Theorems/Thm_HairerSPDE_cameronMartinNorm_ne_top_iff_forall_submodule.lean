-- Prove2me | Theorems.Thm_HairerSPDE_cameronMartinNorm_ne_top_iff_forall_submodule
-- name    : HairerSPDE.cameronMartinNorm_ne_top_iff_forall_submodule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:50:06.102982+00:00
-- url     : https://prove2.me/theorems/8a62fd00-2b0b-4385-a561-0e408ed643d7
-- title:
--   Proposition 4.45: $H_\mu$ is the intersection of all full-measure measurable subspaces
-- statement:
--   **Proposition 4.45: an intrinsic description of the Cameron–Martin space.**
--
--   Let $\mu$ be a centred Gaussian measure on a separable Banach space $B$. Call $V \subseteq B$ a *measurable linear subspace of full measure* if $V$ is a linear subspace of $B$, is Borel measurable, and satisfies $\mu(V) = 1$. Then, for $h \in B$,
--
--   $$ h \in H_\mu \qquad \Longleftrightarrow \qquad h \in V \ \text{ for every measurable linear subspace } V \text{ with } \mu(V)=1 . $$
--
--   In other words $H_\mu$ is exactly the intersection of all measurable linear subspaces of full measure.
--
--   The forward implication is a consequence of the Cameron–Martin theorem: translating a full-measure affine subspace by a Cameron–Martin vector again yields a full-measure set, which is impossible unless the vector lies in the subspace. The converse is a construction: for any $h$ of infinite Cameron–Martin norm one builds, from functionals $\ell_n$ with $C_\mu(\ell_n,\ell_n) \le 1$ and $\ell_n(h) \ge n$, a measurable linear subspace of full measure missing $h$.
--
--   The statement explains why $H_\mu$ is canonical: it is not merely one convenient Hilbert space attached to $\mu$, but the smallest measurable linear subspace one could hope to charge — even though, when it is infinite dimensional, it has $\mu$-measure zero itself.
--
--   **Formalization Note.** "Measurable linear subspace" is a linear subspace of $B$ whose underlying set is Borel measurable; membership in $H_\mu$ is finiteness of the Cameron–Martin norm. Only the first assertion of Proposition 4.45 is claimed; the accompanying statement $\mu(H_\mu)=0$ in the infinite-dimensional case is not part of it.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 32, Proposition 4.45 (first assertion)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem cameronMartinNorm_ne_top_iff_forall_submodule {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) :
    cameronMartinNorm μ h ≠ ∞
      ↔ ∀ V : Submodule ℝ B, MeasurableSet (V : Set B) → μ V = 1 → h ∈ V := by sorry

end HairerSPDE
