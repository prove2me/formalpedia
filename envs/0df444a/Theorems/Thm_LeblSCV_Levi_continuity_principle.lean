-- Prove2me | Theorems.Thm_LeblSCV_Levi_continuity_principle
-- name    : LeblSCV.Levi.continuity_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:14:31.716556+00:00
-- url     : https://prove2.me/theorems/32b72c04-dd05-49ac-a34a-09c3c732a4ed
-- title:
--   Theorem 2.1.7 — Kontinuitätssatz (continuity principle), first version
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open, and let $\varphi_k : \overline{\mathbb{D}} \to \mathbb{C}^n$ be closed analytic discs converging uniformly on $\overline{\mathbb{D}}$ to a closed analytic disc $\varphi$, with $\varphi_k(\overline{\mathbb{D}}) \subset U$ for every $k$ and $\varphi(\partial\mathbb{D}) \subset U$. Then there is $s > 0$ such that for every $f \in \mathcal{O}(U)$ and every $p \in \varphi(\mathbb{D})$ there is $F \in \mathcal{O}(\Delta_s(p))$ with
--   $$F = f \quad\text{on some nonempty open subset of } U \cap \Delta_s(p).$$
--   Here $\Delta_s(p)$ is the polydisc of polyradius $(s,\dots,s)$ centred at $p$. The radius $s$ does not depend on $f$ or $p$.
--
--   The continuity principle says that holomorphic functions continue past the limit disc, even where $\varphi(\mathbb{D})$ leaves $U$.
--
--   **Formalization Note.** $\Delta_s(p)$ is `Metric.ball p s` for the sup norm of `Fin n → ℂ`, which is exactly the polydisc. Uniform convergence is `TendstoUniformlyOn` on `Metric.closedBall 0 1`. "Some open subset" is read as a *nonempty* open subset, the only non-vacuous reading.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 52, Theorem 2.1.7

import Mathlib
import Definitions.Def_LeblSCV_Levi_IsClosedAnalyticDisc

namespace LeblSCV.Levi

/-- Theorem 2.1.7 (Kontinuitätssatz, first version; Lebl, p. 52). `Δ_s(p)` is the polydisc of
radius `s`, i.e. `Metric.ball p s` for the sup norm of `Fin n → ℂ`; `𝔻` is `Metric.ball 0 1`,
`closure 𝔻` is `Metric.closedBall 0 1` and `∂𝔻` is `Metric.sphere 0 1` in `ℂ`. "Some open subset"
is read as a nonempty open subset. -/
theorem continuity_principle {n : ℕ} (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (φs : ℕ → ℂ → (Fin n → ℂ)) (φ : ℂ → (Fin n → ℂ))
    (hφs : ∀ j, IsClosedAnalyticDisc (φs j)) (hφ : IsClosedAnalyticDisc φ)
    (hconv : TendstoUniformlyOn φs φ Filter.atTop (Metric.closedBall (0 : ℂ) 1))
    (hφsU : ∀ j, φs j '' Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hφU : φ '' Metric.sphere (0 : ℂ) 1 ⊆ U) :
    ∃ s : ℝ, 0 < s ∧ ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
      ∀ p ∈ φ '' Metric.ball (0 : ℂ) 1,
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball p s) ∧
          ∃ O : Set (Fin n → ℂ), IsOpen O ∧ O.Nonempty ∧ O ⊆ U ∩ Metric.ball p s ∧
            Set.EqOn F f O := by sorry

end LeblSCV.Levi
