-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_7_4
-- name    : GuardedSSSP.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:15.487214+00:00
-- url     : https://prove2.me/theorems/846c3ff2-639d-456a-be71-4ce2bed4364d
-- title:
--   Lemma 7.4 — uniform packet bound $s+(1+L_1(q)/s)g(s)+(\log_2s)^2=O(F(q))$
-- statement:
--   Write $F=f_d$ and $g=f_{d-1}$. There is an absolute threshold $S_0>0$ such that for all multipliers $0<\kappa_1\le\kappa_2$ there is a constant $C$ with the following property: for every $d\ge1$, every $q\ge0$ and every $s\ge S_0$ with $\kappa_1F(q)\le s\le\kappa_2F(q)$,
--
--   $$s+\Big(1+\frac{L_1(q)}{s}\Big)g(s)+(\log_2s)^2\le C\,F(q).$$
--
--   The constant does not depend on $d$. The bound controls the cost of a lower-generation acquisition by the acquisition rate $f_d(q)$.
--
--   Differences from the source:
--   - reading: s within fixed positive multipliers of F(q), above the absolute base threshold; O(F(q)) with an absolute constant independent of d → ∃ S₀ > 0 ∀ 0 < κ₁ ≤ κ₂ ∃ C ∀ d ≥ 1 ∀ q ≥ 0 ∀ s ≥ S₀ with κ₁F(q) ≤ s ≤ κ₂F(q); reason: the threshold is absolute (chosen before the multipliers), the constant uniform in d
--   - generalization: the quota q (an integer) → every real q ≥ 0; reason: contains the integer quotas
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 7.4, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

/-- **Lemma 7.4** (Uniform packet bound), p.15 (PDF p.16).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Let F = f_d, g = f_{d−1}, and let s be within fixed positive
multipliers of F(q), with s above the absolute base threshold. Then
s + (1 + L₁(q)/s) g(s) + (log₂ s)² = O(F(q)) (28) with an absolute constant independent of d."

There is an absolute threshold `S₀ > 0` such that for all multipliers `0 < κ₁ ≤ κ₂` there is a constant
`C` with: for every `d ≥ 1`, every `q ≥ 0` and every `s ≥ S₀` with `κ₁ f_d(q) ≤ s ≤ κ₂ f_d(q)`,

`s + (1 + L₁(q)/s) f_{d−1}(s) + (log₂ s)² ≤ C f_d(q)`.

**Formalization Note.** The threshold is chosen before the multipliers ("absolute"), the constant after
them and before `d` ("independent of d"). `q` is real; the paper's quota is an integer. `d ≥ 1` because
`g = f_{d−1}`. -/
theorem lemma_7_4 :
    ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ κ₁ κ₂ : ℝ, 0 < κ₁ → κ₁ ≤ κ₂ → ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d →
      ∀ q s : ℝ, 0 ≤ q → S₀ ≤ s → κ₁ * f d q ≤ s → s ≤ κ₂ * f d q →
        s + (1 + L 1 q / s) * f (d - 1) s + Real.logb 2 s ^ 2 ≤ C * f d q := by sorry

end GuardedSSSP
