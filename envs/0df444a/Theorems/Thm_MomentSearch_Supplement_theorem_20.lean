-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_20
-- name    : MomentSearch.Supplement.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:36:14.294333+00:00
-- url     : https://prove2.me/theorems/83572b73-5f02-40eb-aba1-72339fd0369e
-- title:
--   Theorem 20 — every linear sketch $A\in\mathbb R^{k\times n}$ has $\alpha(\mathcal U_{\sigma_A})=\Omega(\log n/\log k)$
-- statement:
--   There is an absolute constant $c>0$ such that for every $n\ge2$, every $k\ge2$ and every matrix $A\in\mathbb R^{k\times n}$, the uncertainty collection $\mathcal U_{\sigma_A}$ of the linear sketch $\sigma_A(p)=Ap$ satisfies
--   $$\alpha(\mathcal U_{\sigma_A})\ge c\,\frac{\log n}{\log k}.$$
--
--   Thus $n^{\Omega(\varepsilon)}$ exact linear measurements are necessary for an $O(1/\varepsilon)$-approximation; the dyadic sketch of Theorem 27 shows this is tight up to the constant in the exponent and polylogarithmic factors.
--
--   Differences from the source:
--   - encoding: α(𝒰_{σ_A}) = Ω(log n / log k) → ∃ c > 0 chosen before n, k, A with ENNReal.ofReal (c·log₂ n / log₂ k) ≤ α(𝒰_{σ_A}); reason: Ω hides an absolute constant; the ratio of logarithms is base-independent
--   - encoding: A ∈ ℝ^{k×n} (n the path length) → n ≥ 2 as a hypothesis; reason: the paper's standing assumption n ≥ 2 (§2.1)
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 20, p.16 (PDF p.18); restated with proof App. D.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection

open scoped ENNReal

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 20** (Linear sketch lower bound) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 20, p.16 (PDF p.18); restated with
proof App. D.1, p.33 (PDF p.35)).

There is an absolute constant `c > 0` such that for every `n ≥ 2`, every `k ≥ 2` and every
matrix `A ∈ ℝ^{k×n}`, the uncertainty collection of the linear sketch `σ_A(p) = Ap` satisfies
`α(𝒰_{σ_A}) ≥ c · log n / log k`.

**Formalization Note.** `Ω(·)` is an absolute constant chosen before `n`, `k`, `A`; no relation
between `k` and `n` is assumed. `log` is base 2 (the ratio is base-independent). -/
theorem theorem_20 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (k : ℕ), 2 ≤ k → ∀ A : Matrix (Fin k) (Fin n) ℝ,
        ENNReal.ofReal (c * Real.logb 2 n / Real.logb 2 k) ≤
          approxFactor (sketchCollection (fun p : Fin n → ℝ => Matrix.mulVec A p)) := by sorry

end MomentSearch.Supplement
