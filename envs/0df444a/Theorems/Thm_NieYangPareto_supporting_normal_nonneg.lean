-- Prove2me | Theorems.Thm_NieYangPareto_supporting_normal_nonneg
-- name    : NieYangPareto.supporting_normal_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:29.946276+00:00
-- url     : https://prove2.me/theorems/a24de01b-5f53-4503-87e3-c91edb880b28
-- title:
--   §3.1 — the normal of a supporting hyperplane for $\mathcal U$ is nonnegative
-- statement:
--   For a nonzero vector $w\in\mathbb R^m$ and $b\in\mathbb R$, the hyperplane $H=\{u: w^Tu=b\}$ is a **supporting hyperplane** for $\mathcal U$ if $b=\inf_{u\in\mathcal U}w^Tu$. If $H$ is one, then
--
--   $$
--   w\ge 0 .
--   $$
--
--   Because $\mathcal U$ contains the orthant $f(x)+\mathbb R^m_+$, a coordinate of $w$ cannot be negative.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: b = inf_{u∈𝒰} wᵀu, b ∈ ℝ → IsGLB of the image of 𝒰 under u ↦ wᵀu; reason: a real infimum that exists; a set empty or unbounded below has no such b, so the junk value of real sInf cannot enter
--   - reading: "𝒰 contains f(x) + ℝⁿ_+" → no such hypothesis: the claim is about 𝒰 itself, which contains f(x) + ℝ^m_+; reason: ℝⁿ_+ is a slip for ℝ^m_+: the sum only typechecks in ℝ^m
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3.1, p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U

namespace NieYangPareto

/-- **The normal of a supporting hyperplane is nonnegative.** Nie–Yang, arXiv:2108.04336v2, §3.1, p.6:
"Since 𝒰 contains f(x) + ℝⁿ_+, the normal w must be nonnegative, for H to be a supporting hyperplane."

For nonzero `w ∈ ℝ^m` and `b ∈ ℝ`, `H = {u : wᵀu = b}` is a supporting hyperplane for `𝒰` if
`b = inf_{u ∈ 𝒰} wᵀu` (p.6).

**Formalization Note** The infimum with real value `b` is `IsGLB`, so a set unbounded below, or empty,
has no such `b`. The page's `ℝⁿ_+` is a slip for `ℝ^m_+`: only that sum typechecks in `ℝ^m`. -/
theorem supporting_normal_nonneg {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (w : Fin m → ℝ) (b : ℝ) (hw : w ≠ 0)
    (hb : IsGLB ((fun u => w ⬝ᵥ u) '' P.U) b) :
    0 ≤ w := by sorry

end NieYangPareto
