-- Prove2me | Theorems.Thm_FrechetPrefs_psi_strictMono
-- name    : FrechetPrefs.psi_strictMono
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:05.73911+00:00
-- url     : https://prove2.me/theorems/e92aff0f-c4af-426b-b939-fbe4d04e3446
-- title:
--   (EC.7)–(EC.8), p.ec6 — $\psi$ is increasing on $[K,\infty)$ for $\theta\ge|u''(K)|$, strictly for $\theta>|u''(K)|$
-- statement:
--   Let $u$ satisfy Assumption 1, $K>0$ and $\theta>0$, and let $\psi(x)=\frac1\theta u'(x)+x$.
--
--   (a) If $|u''(K)|\le\theta$ (EC.8), then for every $x\ge K$
--   $$1+\frac1\theta u''(x)\ge 0$$
--   (that is, (EC.7) holds on $[K,\infty)$), and $\psi$ is increasing on $[K,\infty)$.
--
--   (b) If $|u''(K)|<\theta$, then $1+\frac1\theta u''(x)>0$, that is $\psi'(x)>0$, for every $x\ge K$, and $\psi$ is strictly increasing on $[K,\infty)$.
--
--   This is the monotonicity which makes the solution of (5) a quantile function.
--
--   Differences from the source:
--   - generalization: the floor K* = minᵢ Kᵢ and points g(s) > K* → any K > 0 and every x ≥ K; reason: it specializes to K = K*, and the points g(s) are among the x ≥ K*
--   - generalization: (EC.8) gives (EC.7) only → also the strict clause (b) for θ > |u″(K)|; reason: an added conclusion; clause (a) is the printed claim
--   - reading: "x ↦ |u″(x)| is decreasing", with the strict intermediate bound |u″(g(s))| < |u″(K*)| → |u″| weakly decreasing, intermediate bound not stated; reason: the strict bound fails where |u″| is constant, and the printed conclusion (EC.7) does not need it
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), (EC.7)–(EC.8), p.ec6

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- (EC.7)–(EC.8), p.ec6 of manuscript MS-DEC-19-01009-REV: for `θ > 0` with `|u″(K)| ≤ θ` (EC.8),
`1 + (1/θ) u″(x) ≥ 0` on `[K,∞)` (EC.7), so `ψ(x) = (1/θ) u′(x) + x` is increasing there; for
`θ > |u″(K)|` the inequality is strict and `ψ` is strictly increasing on `[K,∞)`.

**Formalization Note.** `|u″|` is only weakly decreasing (Assumption 1), so the page's intermediate
strict bound `|u″(g(s))| < |u″(K*)|` is not stated; strictness of `ψ` comes from `θ > |u″(K)|`. -/
theorem psi_strictMono (u : ℝ → ℝ) (hu : IsInadaUtility u) (K θ : ℝ) (hK0 : 0 < K)
    (hθ0 : 0 < θ) :
    (|deriv (deriv u) K| ≤ θ →
      (∀ x, K ≤ x → 0 ≤ 1 + 1 / θ * deriv (deriv u) x) ∧
      MonotoneOn (psi u θ) (Ici K)) ∧
    (|deriv (deriv u) K| < θ →
      (∀ x, K ≤ x → 0 < 1 + 1 / θ * deriv (deriv u) x) ∧
      (∀ x, K ≤ x → 0 < deriv (psi u θ) x) ∧
      StrictMonoOn (psi u θ) (Ici K)) := by sorry

end FrechetPrefs
