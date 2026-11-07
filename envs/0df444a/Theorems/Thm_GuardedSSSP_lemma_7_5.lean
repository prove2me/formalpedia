-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_7_5
-- name    : GuardedSSSP.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:35.322255+00:00
-- url     : https://prove2.me/theorems/bbd2ada3-42db-4dc5-b0c1-3144875deb67
-- title:
--   Lemma 7.5 — uniform root balance (29)
-- statement:
--   There is an absolute scale $X_0$ such that for all multipliers $0<\kappa_1\le\kappa_2$ there is $C>0$ with the following property: for every $d\ge1$, every $x\ge X_0$ and every $t$ with $\kappa_1f_d(x)\le t\le\kappa_2f_d(x)$,
--
--   $$t^2\le C\,L_1(x)f_{d-1}(t),\qquad L_1(x)f_{d-1}(t)\le C\,t^2,\qquad t+\frac{L_1(x)}{t}f_{d-1}(t)+(\log_2t)^2\le C\,f_d(x).$$
--
--   Choosing the main width $t=\Theta(f_d(x))$ therefore balances the width against the lower-generation work, uniformly in $d$.
--
--   Differences from the source:
--   - reading: if t = Θ(f_d(x)) with fixed multipliers, then above an absolute scale t² = Θ(L₁(x)f_{d−1}(t)) and (29) = O(f_d(x)), uniformly in d → ∃ X₀ ∀ 0 < κ₁ ≤ κ₂ ∃ C > 0 ∀ d ≥ 1 ∀ x ≥ X₀ ∀ t ∈ [κ₁f_d(x), κ₂f_d(x)]: the three bounds; reason: the scale is absolute (before the multipliers), the constant uniform in d
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 7.5, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

/-- **Lemma 7.5** (Uniform root balance), p.16 (PDF p.17).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "If t = Θ(f_d(x)) with fixed multipliers, then, above an
absolute scale, t² = Θ(L₁(x) f_{d−1}(t)), t + (L₁(x)/t) f_{d−1}(t) + (log₂ t)² = O(f_d(x)), (29)
uniformly in d."

There is an absolute scale `X₀` such that for all multipliers `0 < κ₁ ≤ κ₂` there is `C > 0` with: for
every `d ≥ 1`, every `x ≥ X₀` and every `t` with `κ₁ f_d(x) ≤ t ≤ κ₂ f_d(x)`,
1. `t² ≤ C·L₁(x) f_{d−1}(t)` and `L₁(x) f_{d−1}(t) ≤ C·t²`;
2. `t + (L₁(x)/t) f_{d−1}(t) + (log₂ t)² ≤ C f_d(x)`.

**Formalization Note.** The scale is chosen before the multipliers ("absolute"), the constant after them
and before `d` ("uniformly in d"). `d ≥ 1` because `f_{d−1}` appears. -/
theorem lemma_7_5 :
    ∃ X₀ : ℝ, ∀ κ₁ κ₂ : ℝ, 0 < κ₁ → κ₁ ≤ κ₂ → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ x t : ℝ, X₀ ≤ x → κ₁ * f d x ≤ t → t ≤ κ₂ * f d x →
        t ^ 2 ≤ C * (L 1 x * f (d - 1) t) ∧ L 1 x * f (d - 1) t ≤ C * t ^ 2 ∧
        t + L 1 x / t * f (d - 1) t + Real.logb 2 t ^ 2 ≤ C * f d x := by sorry

end GuardedSSSP
