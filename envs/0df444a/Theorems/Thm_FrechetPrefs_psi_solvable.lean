-- Prove2me | Theorems.Thm_FrechetPrefs_psi_solvable
-- name    : FrechetPrefs.psi_solvable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:14.146768+00:00
-- url     : https://prove2.me/theorems/ab0c5f33-9bff-42bf-834d-97611369aac0
-- title:
--   (EC.9)–(EC.10), p.ec6 — equation $\psi(x)=z$ is solvable above the floor
-- statement:
--   Let $u$ satisfy Assumption 1, $0<K<K_B$, and $\theta$ with $|u''(K)|\le\theta$ (EC.8) and $\theta>u'(K)/(K_B-K)$ (EC.10); every $\theta>\theta_c=\max\{|u''(K)|,u'(K)/(K_B-K)\}$ qualifies. Then $\psi(K)<K_B$, and for every $z\ge K_B$ the equation
--   $$\psi(x)=\frac1\theta u'(x)+x=z$$
--   has a solution $x\in(K,z]$, which is the only solution in $[K,\infty)$.
--
--   This is condition (i) of the proof: equation (EC.6) can be solved for every value of the right side $g_B(s)\ge K_B$.
--
--   Differences from the source:
--   - generalization: solution for any z > K_B → solution for every z ≥ K_B; reason: the same page says the right side satisfies g_B(s) ≥ K_B, and ψ(K) < K_B covers z = K_B
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with conditions |u″(K)| ≤ θ and θ > u′(K)/(K_B − K); reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), (EC.9)–(EC.10), p.ec6

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- (EC.9)–(EC.10), p.ec6 of manuscript MS-DEC-19-01009-REV: for `θ` satisfying (EC.8),
`|u″(K)| ≤ θ`, and (EC.10), `θ > u′(K)/(K_B − K)`, one has `ψ(K) < K_B`, and for every `z ≥ K_B` the
equation `ψ(x) = z` has a solution `x ∈ (K, z]`, the only solution in `[K,∞)`.

**Formalization Note.** `KBv` is any real above `K`, in particular `K_B`. The page writes `z > K_B`,
while the case `z = g_B(s) ≥ K_B` is what occurs. Every `θ > θ_c` of (EC.11) satisfies both
hypotheses. -/
theorem psi_solvable (u : ℝ → ℝ) (hu : IsInadaUtility u) (K KBv θ : ℝ) (hK0 : 0 < K)
    (hK : K < KBv) (hθ8 : |deriv (deriv u) K| ≤ θ) (hθ10 : deriv u K / (KBv - K) < θ) :
    psi u θ K < KBv ∧
    ∀ z, KBv ≤ z → ∃ x, (K < x ∧ x ≤ z ∧ psi u θ x = z) ∧
      ∀ y, K ≤ y → psi u θ y = z → y = x := by sorry

end FrechetPrefs
