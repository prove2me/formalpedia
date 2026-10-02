-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_proper_iff_cluster_points_in_frontier
-- name    : LeblSCV.BallPolydisc.proper_iff_cluster_points_in_frontier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:20:19.73783+00:00
-- url     : https://prove2.me/theorems/3dbc85de-04d5-466b-9216-bbefbae6b6d0
-- title:
--   Lemma 1.4.7 — proper maps take the boundary to the boundary
-- statement:
--   Let $U \subset \mathbb{R}^n$ and $V \subset \mathbb{R}^m$ be bounded domains and let $f : U \to V$ be continuous. Then $f$ is proper if and only if, for every sequence $\{p_k\}$ in $U$ with $p_k \to p \in \partial U$, every limit point of the sequence $\{f(p_k)\}$ lies in $\partial V$:
--   $$f \text{ proper} \iff \Big( p_k \in U,\ p_k \to p \in \partial U,\ q \text{ a limit point of } \{f(p_k)\} \implies q \in \partial V \Big).$$
--
--   This makes precise the slogan that a proper map "takes the boundary to the boundary", and is the form in which properness enters the proof of Theorem 1.4.8.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `Fin n → ℝ` (boundedness and topological boundary do not depend on the choice of norm). A domain is open, connected and nonempty. "Proper" is `IsProperMapOn f U V` (Definition 1.4.3 for the restricted map $U \to V$). A limit point of the sequence $\{f(p_k)\}$ is a cluster point of the sequence, `MapClusterPt q atTop (fun k => f (p k))` (equivalently, the limit of a convergent subsequence).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 34, Lemma 1.4.7

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn

open Filter Topology

namespace LeblSCV.BallPolydisc

/-- Lemma 1.4.7 (Lebl, p. 34). For bounded domains `U ⊆ ℝⁿ`, `V ⊆ ℝᵐ` and a continuous
`f : U → V`, `f` is proper iff for every sequence `p_k` in `U` converging to a point of `∂U`,
every limit point of `f(p_k)` lies in `∂V`. -/
theorem proper_iff_cluster_points_in_frontier {n m : ℕ}
    (U : Set (Fin n → ℝ)) (V : Set (Fin m → ℝ))
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (hfUV : Set.MapsTo f U V) (hf : ContinuousOn f U) :
    IsProperMapOn f U V ↔
      ∀ (p : ℕ → (Fin n → ℝ)) (x : Fin n → ℝ), (∀ k, p k ∈ U) →
        Tendsto p atTop (𝓝 x) → x ∈ frontier U →
          ∀ q : Fin m → ℝ, MapClusterPt q atTop (fun k => f (p k)) → q ∈ frontier V := by sorry

end LeblSCV.BallPolydisc
