-- Prove2me | Theorems.Thm_KarlinDP_Deterministic_totalYield_shift
-- name    : KarlinDP.Deterministic.totalYield_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:16:22.596235+00:00
-- url     : https://prove2.me/theorems/16d7a01e-db56-46cb-89d1-d667b4a5eb4d
-- title:
--   Shift identity (p. 290) — Φ(ω, s) = L(ω, δ₁) + P(δ₁) Φ(T_{δ₁} ω, s′)
-- statement:
--   In the setting of Karlin's deterministic model ($\Omega$ Hausdorff, $D$ nonempty compact Hausdorff, $L \ge 0$ continuous on $\Omega \times D$, $(\delta, \omega) \mapsto T_\delta\,\omega$ continuous, $P > 0$ continuous, $\omega_1 = \omega$, $\omega_n = T_{\delta_{n-1}}\,\omega_{n-1}$, $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$), let $\omega \in \Omega$ and let $s = (\delta_1, \delta_2, \dots)$ be a strategy whose yield series $\sum_{n} L(\omega_n, \delta_n) P_n(s)$ converges. Write $s' = (\delta_2, \delta_3, \dots)$ for the shifted strategy. Then
--   $$\Phi(\omega, s) = L(\omega, \delta_1) + P(\delta_1)\, \Phi(T_{\delta_1}\,\omega, s').$$
--
--   The identity splits off the first stage: after the first decision, the remaining yield is the yield of the shifted strategy from the next state, scaled by $P(\delta_1)$. It is the step from which the functional equation (2) is derived.
--
--   **Formalization Note** The shift is `fun k => s (k + 1)`. The paper states the identity inside a maximum over $s$; this item is the pointwise identity for each $s$. Summability of the series for this particular $s$ is assumed; it follows from the uniform convergence (1) and is needed because Lean's `tsum` of a non-summable series is $0$. The model's standing hypotheses (continuity, compactness, joint continuity of $T$ as in Theorem 1) are kept as in every item of the mission.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, p. 290, §Functional Equation for the Optimal Strategy, first display (lines 2–3; printed slip Π P(δ_1) read as Π P(δ_i))

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

namespace KarlinDP.Deterministic

/-- The shift identity (Karlin 1955, p. 290, first display): for every strategy
`s = (δ₁, δ₂, …)` whose yield series is summable, with `s' = (δ₂, δ₃, …)`,
`Φ(ω, s) = L(ω, δ₁) + P(δ₁) Φ(T_{δ₁} ω, s')`. -/
theorem totalYield_shift {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (ω : Ω) (s : ℕ → D)
    (hsum : Summable (fun n => L (trajectory T ω s n) (s n) * weight P s n)) :
    totalYield L T P ω s
      = L ω (s 0) + P (s 0) * totalYield L T P (T (s 0) ω) (fun k => s (k + 1)) := by sorry

end KarlinDP.Deterministic
