-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_escapes_of_bounded_reciprocal_and_unbounded
-- name    : MilnorDynamics.exists_subseq_escapes_of_bounded_reciprocal_and_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-10-03T14:14:39.359504+00:00
-- url     : https://prove2.me/theorems/d64dae70-bfbc-410c-b851-f30e040bacfb
-- title:
--   Bounded reciprocals plus non-local-boundedness force escape to infinity
-- statement:
--   Let $U\subset\mathbb C$ be open and connected, and let $(f_n)$ be holomorphic maps $U\to\mathbb C\setminus\{0,1\}$. Suppose two things about the family. First, the reciprocals are locally bounded: for every compact $K\subset U$ there is an $M$ with $|1/f_n(z)|\le M$ for all $n$ and all $z\in K$. Second, the family $(f_n)$ itself is *not* locally bounded: for some compact $K\subset U$ there is no single $M$ with $|f_n(z)|\le M$ for all $n$ and all $z\in K$.
--
--   $$\exists\,\varphi:\mathbb N\to\mathbb N\ \text{strictly increasing}\quad \forall K\subset U\ \text{compact}\ \forall R>0\ \exists N\ \forall n\ge N\ \forall z\in K:\quad R<|f_{\varphi(n)}(z)|.$$
--
--   The family then escapes to infinity uniformly on every compact subset of $U$, and one single subsequence $\varphi$ serves all compact sets at once.
--
--   Both hypotheses are necessary. Boundedness of the reciprocals alone does not force escape: the constant family $f_n\equiv 2+1/(n+1)$ omits $0$ and $1$, has reciprocals bounded by $1/2$, and yet $|f_n z|\le 2.5<3$ for every $n$, so no subsequence escapes the disk of radius $3$. Conversely non-local-boundedness alone does not force escape either: the polynomials $f_n(z)=n-n^2z$ omit nothing that excludes them, are unbounded on $[0,1]$, and vanish at $z=1/n$, so no subsequence escapes.
--
--   What makes the conclusion work is that the two hypotheses kill opposite branches of Hurwitz's theorem. Passing to the reciprocals $h_n=1/f_n$, the local boundedness of $h_n$ gives a subsequence converging locally uniformly on $U$ to a continuous limit $h$, which is moreover holomorphic. Since $h_n$ omits $0$, Hurwitz forces either $h\equiv 0$ or $h$ is nowhere zero on the connected set $U$. The second alternative would make $|h|$ bounded away from $0$ on every compact subset of $U$, hence $|f_n|=|1/h_n|$ bounded on each compact, contradicting the non-local-boundedness hypothesis. Hence $h\equiv 0$, that is $\sup_{z\in K}|h_{\varphi(n)}(z)|\to0$ for every compact $K$, which is exactly $|f_{\varphi(n)}|\to\infty$ uniformly on each compact.
--
--   **Formalization Note.** The two auxiliary facts used from Milnor's argument are the proved platform theorems `MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform` and `MilnorDynamics.limit_avoids_or_const`.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_escapes_of_bounded_reciprocal_and_unbounded (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hrecip : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖(f n)⁻¹ z‖ ≤ M)
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖ := by sorry

end MilnorDynamics
