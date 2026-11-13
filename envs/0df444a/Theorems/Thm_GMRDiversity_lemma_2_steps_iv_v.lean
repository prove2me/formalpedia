-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_steps_iv_v
-- name    : GMRDiversity.lemma_2_steps_iv_v
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:38:28.967515+00:00
-- url     : https://prove2.me/theorems/cc1d6233-4b62-46ee-a634-a72f718e3a7a
-- title:
--   Proof of Lemma 2, Steps (iv)–(v) — screening: a wrong guess passes w.p. $1/2$, $f=\frac{2\rho}{1+\rho}\le\frac\eta4$
-- statement:
--   A guess $\widehat x$ is tested with a fresh equation $(v,\alpha)$, $v$ uniform on $\mathbb F_2^n$ and $\alpha=v\cdot x$, and passes when $v\cdot\widehat x=\alpha$.
--
--   1. A correct guess always passes.
--   2. A wrong guess $\widehat x\ne x$ passes for exactly half of the vectors $v$, i.e. with probability $1/2$.
--   3. If $\rho>0$ and $f=\rho+\frac{1-\rho}{2}f$, then $f=2\rho/(1+\rho)$.
--   4. For $\eta>0$ and $\rho:=\eta/8$, $\;2\rho/(1+\rho)\le\eta/4$.
--
--   Here $f$ is the probability that a wrong guess is accepted before it is rejected, when each screening step accepts with probability $\rho$ and otherwise runs one test.
--
--   Differences from the source:
--   - encoding: a wrong guess passes independently with probability 1/2 → 2 · #{v : v · x̂ = v · x} = 2^n for x̂ ≠ x; reason: v is uniform, so the probability is the count over 2^n
--   - generalization: η = 2^{−d−1} ∈ (0, 1] → every η > 0; reason: the inequality holds for all positive η; the page's η is positive
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Steps (iv)–(v), p.11

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2, Steps (iv)–(v): screening** (Brandenberger, Doron-Arad, Mossel, *Genetic
Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…,
proof of Lemma 2, Steps (iv)–(v), p.11): a guess `x̂` is tested with a fresh equation `(v, α)`,
`v` uniform and `α = v · x`, and passes when `v · x̂ = α`.
1. A correct guess always passes.
2. A wrong guess passes for exactly half of the `v`, i.e. with probability `1/2`.
3. If `ρ > 0` and `f = ρ + ((1 − ρ)/2) f`, then `f = 2ρ/(1 + ρ)`.
4. With `ρ := η/8` and `η > 0`, `2ρ/(1 + ρ) ≤ η/4`. -/
theorem lemma_2_steps_iv_v {n : ℕ} (x xhat : V n) :
    (xhat = x → ∀ v : V n, dot v xhat = dot v x) ∧
    (xhat ≠ x → 2 * Nat.card {v : V n // dot v xhat = dot v x} = 2 ^ n) ∧
    (∀ ρ f : ℝ, 0 < ρ → f = ρ + (1 - ρ) / 2 * f → f = 2 * ρ / (1 + ρ)) ∧
    (∀ η : ℝ, 0 < η → 2 * (η / 8) / (1 + η / 8) ≤ η / 4) := by sorry

end GMRDiversity
