-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_restrict_ne_top_of_forall_norm_le
-- name    : JHolomorphic.eLpNorm_restrict_ne_top_of_forall_norm_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:25:11.238433+00:00
-- url     : https://prove2.me/theorems/76c31d66-b672-4a07-a70b-405869599858
-- title:
--   A function bounded on a compact subset of $\mathbb C$ has finite $L^q$ norm there
-- statement:
--   Let $F$ be a normed space, $f:\mathbb C\to F$, $K\subseteq\mathbb C$ compact, $q\in[0,\infty]$ and $B\in\mathbb R$ with $\|f(x)\|\le B$ for all $x\in K$. Then $\|f\|_{L^q(K)}<\infty$.
--
--   **Formalization Note** The conclusion is `eLpNorm f q (volume.restrict K) ≠ ⊤` with `q : ℝ≥0∞`; no measurability of `f` is assumed.
-- source:
--   Elementary measure theory; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- A function bounded on a compact set `K ⊆ ℂ` has finite `L^q` norm on `K`. -/
theorem eLpNorm_restrict_ne_top_of_forall_norm_le {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} {K : Set ℂ} (hK : IsCompact K) (q : ℝ≥0∞) {B : ℝ}
    (hB : ∀ x ∈ K, ‖f x‖ ≤ B) : eLpNorm f q (volume.restrict K) ≠ ⊤ := by
  sorry

end JHolomorphic
