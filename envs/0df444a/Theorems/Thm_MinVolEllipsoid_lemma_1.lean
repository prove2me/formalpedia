-- Prove2me | Theorems.Thm_MinVolEllipsoid_lemma_1
-- name    : MinVolEllipsoid.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:27.769121+00:00
-- url     : https://prove2.me/theorems/da7a1ff8-2488-4f75-9e48-f71c300a19e1
-- title:
--   Lemma 1: $[x;\tau]\in\mathcal K$ implies $\tau\ge0$, and $\tau=0$ only if $x=0$
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). If $[x;\tau]\in\mathcal K$ with $x\in\mathbb R^K$, $\tau\in\mathbb R$, then
--
--   $$
--   \tau\ge0,\qquad\text{and}\qquad\tau=0\ \Longrightarrow\ x=0.
--   $$
--
--   The last coordinate of a point of $\mathcal K$ thus measures how far the point is from the apex; it is the fact behind the pointedness of $\mathcal K$ (Lemma 2) and behind the identification $\mathcal P=\{x:[x;1]\in\mathcal K\}$.
--
--   The cone is the one of display (2), which the paper defines inside Theorem 1 under Assumption 1; the Lean statement carries Assumption 1 as hypotheses accordingly.
--
--   Differences from the source:
--
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 1, p.6

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone

namespace MinVolEllipsoid

/-- **Lemma 1** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 1, p.6). Let `𝒦` be the cone
defined in (2). If `[x; τ] ∈ 𝒦`, then `τ ≥ 0`. Furthermore, `τ = 0` only if `x = 0`.

Here `𝒦 = liftCone P` for a set `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1): compact, convex and with
nonempty interior; (2) is stated under that standing hypothesis of Theorem 1 (p.6).

**Formalization Note** `[x; τ]` is `Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ`, the paper's last
coordinate being the `Unit` coordinate. -/
theorem lemma_1 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (x : Fin n → ℝ) (τ : ℝ)
    (hx : (Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ) ∈ liftCone P) :
    0 ≤ τ ∧ (τ = 0 → x = 0) := by sorry

end MinVolEllipsoid
