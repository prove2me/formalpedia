-- Prove2me | Theorems.Thm_MilnorDynamics_locally_bounded_of_bounded_at_point
-- name    : MilnorDynamics.locally_bounded_of_bounded_at_point
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T14:49:05.32001+00:00
-- url     : https://prove2.me/theorems/cbf28e8f-24ca-4afe-9e7c-026aa989a381
-- title:
--   Rigidity of holomorphic families omitting two values: boundedness at one point forces local boundedness
-- statement:
--   **Rigidity of families omitting two values (Schottky).** Let $U\subseteq\mathbb C$ be a connected open set and let $f_n : U \to \mathbb C\setminus\{0,1\}$ be holomorphic. If the family $(f_n)$ is bounded at a single point of $U$ --- that is, there are $z_0 \in U$ and $M$ with $|f_n(z_0)| \le M$ for every $n$ --- then it is locally bounded: for every compact $K \subseteq U$ there is $M'$ with $|f_n(z)| \le M'$ for every $n$ and every $z \in K$.
--
--   This is the rigidity that makes the escape step of Montel's theorem work. Its content is Schottky's theorem: for a holomorphic $g$ on the unit disc omitting $0$ and $1$, the bound at the centre controls $g$ on every smaller disc by a constant depending only on the centre value and the radius. Applying that to each $f_n$ on a small disc around $z_0$ gives a uniform bound in $n$ on a neighbourhood of $z_0$; the set of points at which the family is locally bounded is then both open and closed in the connected domain $U$, hence all of $U$, and compactness of $K$ turns local boundedness into a single bound.
--
--   Contrapositive form, used below: if the family is not locally bounded on $U$, then it is unbounded at every point of $U$. This is the qualitative half of the escape argument for MilnorDynamics.exists_subseq_escapes_locally.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (the escape step in the proof of Montel's theorem); the underlying rigidity is Schottky's theorem, i.e. the compactness of families of holomorphic functions omitting two values. This is the rigidity named in the source note of MilnorDynamics.exists_subseq_escapes_locally.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem locally_bounded_of_bounded_at_point (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hpt : ∃ z₀ ∈ U, ∃ M : ℝ, ∀ n, ‖f n z₀‖ ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ M' : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M' := by sorry

end MilnorDynamics
