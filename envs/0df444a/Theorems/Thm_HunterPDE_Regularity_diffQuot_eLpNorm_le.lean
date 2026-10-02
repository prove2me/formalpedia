-- Prove2me | Theorems.Thm_HunterPDE_Regularity_diffQuot_eLpNorm_le
-- name    : HunterPDE.Regularity.diffQuot_eLpNorm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:29:58.94482+00:00
-- url     : https://prove2.me/theorems/2d030eb8-d829-444b-9cb3-f26515d92673
-- title:
--   Theorem 4.53 (1) — Lᵖ bound on difference quotients by the weak derivative
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, $\Omega' \Subset \Omega$ and $d = \operatorname{dist}(\Omega', \partial\Omega) > 0$. Let $1 \le p < \infty$ and let $u \in L^1_{\mathrm{loc}}(\Omega)$ have weak first partial derivatives $\partial_i u \in L^p(\Omega)$. Then for $0 < |h| < d$ and every $i$,
--   $$\|D_i^h u\|_{L^p(\Omega')} \le \|\partial_i u\|_{L^p(\Omega)} .$$
--
--   Uniform $L^p$ bounds on difference quotients are what the regularity proof extracts from the equation; this is the direction that turns weak derivatives into such bounds.
--
--   **Formalization Note.** The bound is stated componentwise, which is what the book's proof establishes and what the proof of Theorem 4.27 uses. The printed form $\|D^h u\|_{L^p(\Omega')} \le \|Du\|_{L^p(\Omega)}$ with Euclidean vector lengths fails for large $p$ (take $u(x) = \max(x_1, x_2)$ in $\mathbb{R}^2$). The distance $d$ is modelled as any $d > 0$ with $B(x, d) \subseteq \Omega$ for every $x \in \Omega'$; the largest such $d$ is $\operatorname{dist}(\Omega', \partial\Omega)$ (or $+\infty$ when $\Omega = \mathbb{R}^n$), so quantifying over all of them is the book's condition. `Du i` is a weak $\partial_i u$ on $\Omega$ (0-based `i`), and $p$ is `p : ℝ≥0∞` with `1 ≤ p`, `p ≠ ∞`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 125, Theorem 4.53 (1)

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Theorem 4.53 (1) of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 125: let `Ω ⊂ ℝⁿ` be open,
`Ω′ ⋐ Ω`, `d = dist(Ω′, ∂Ω) > 0`. If `Du ∈ Lᵖ(Ω)` with `1 ≤ p < ∞` and `0 < |h| < d`, then the
difference quotients are bounded in `Lᵖ(Ω′)` by the weak derivatives in `Lᵖ(Ω)`.
`Du ∈ Lᵖ(Ω)` means: `u ∈ L¹_loc(Ω)` has weak first partial derivatives `Du i = ∂ᵢu` on `Ω`, each
in `Lᵖ(Ω)`. The distance `d` is modelled by any `d > 0` with `B(x, d) ⊆ Ω` for all `x ∈ Ω′`; the
book's `dist(Ω′, ∂Ω)` is the largest such `d` (and `+∞` when `Ω = ℝⁿ`), so ranging over all of
them is the book's condition `0 < |h| < dist(Ω′, ∂Ω)`.
The bound is stated componentwise, `‖D_i^h u‖_{Lᵖ(Ω′)} ≤ ‖∂ᵢu‖_{Lᵖ(Ω)}` for every `i`, which is
what the book's proof establishes and what the proof of Theorem 4.27 uses; the printed
vector form `‖D^h u‖_{Lᵖ(Ω′)} ≤ ‖Du‖_{Lᵖ(Ω)}` with Euclidean vector norms fails for large `p`
(`u = max(x₁, x₂)` in `ℝ²`). -/
theorem diffQuot_eLpNorm_le {n : ℕ} (Ω Ω' : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩ' : CompactlyContained Ω' Ω) (d : ℝ) (hd : 0 < d)
    (hdist : ∀ x ∈ Ω', Metric.ball x d ⊆ Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hDu : ∀ i, Shared.HasWeakDeriv Ω (Pi.single i 1) u (Du i))
    (hDu_Lp : ∀ i, MemLp (Du i) p (volume.restrict Ω))
    (h : ℝ) (hh : 0 < |h|) (hhd : |h| < d) (i : Fin n) :
    eLpNorm (diffQuot i h u) p (volume.restrict Ω') ≤ eLpNorm (Du i) p (volume.restrict Ω) := by sorry

end HunterPDE.Regularity
