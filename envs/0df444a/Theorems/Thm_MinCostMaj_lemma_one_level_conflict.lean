-- Prove2me | Theorems.Thm_MinCostMaj_lemma_one_level_conflict
-- name    : MinCostMaj.lemma_one_level_conflict
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:39.890729+00:00
-- url     : https://prove2.me/theorems/d5990d48-b475-46b5-941a-a45b2684038d
-- title:
--   Lemma "One-level conflict bound" — $\Pr[v\mapsto a \text{ conflicts with } t_i]\le 2^{|A|+i}\lambda_v(a)$
-- statement:
--   Fix a variable $v$ with potato $A^J_v$ and LP marginals $\lambda_v$ (a probability vector on $A^J_v$), a value $a\in A^J_v$ and $i\ge1$. Over the random thresholds $t_j\sim\mathrm{Unif}[2^{-j},2^{-(j-1)}]$ (independent),
--   $$\Pr\big[v\mapsto a\text{ conflicts with }t_i\big]\le2^{|A|+i}\,\lambda_v(a),$$
--   where $|A|$ is the size of the domain.
--
--   It is the basic estimate behind the tail bound on the levels.
--
--   Differences from the source:
--   - encoding: LP marginal λ_v of the BLP of J → any probability vector on A^J_v (nonnegative, zero off A^J_v, total mass 1); reason: the BLP marginals are exactly such vectors and the lemma uses nothing else about them
--   - encoding: Pr → the measure of the event under the product law `thresholdMeasure`, in [0, ∞]; reason: same probability
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "One-level conflict bound", p.20 (PDF p.21)

import Mathlib
import Definitions.Def_MinCostMaj_Levels
import Definitions.Def_MinCostMaj_thresholdLaw

namespace MinCostMaj

/-- **Lemma "One-level conflict bound"**, p.20 (PDF p.21).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Lemma "One-level conflict bound", p.20: "For every fixed v, a ∈ A^J_v, and i ≥ 1,
Pr[v ↦ a conflicts with ti] ≤ 2^{|A|+i} λv(a)."

`S = A^J_v ⊆ D`, `lam = λᵥ` a probability vector on `S` (an LP marginal), `|A| = |D|`, and the
probability is over the threshold law `thresholdMeasure` (`tᵢ ∼ Unif[2^{−i}, 2^{−(i−1)}]`
independently).

**Formalization Note.** The probability is an `ℝ≥0∞` value; the bound is written with
`ENNReal.ofReal`. -/
theorem lemma_one_level_conflict {D : Type*} [Fintype D] [DecidableEq D] (S : Finset D)
    (lam : D → ℝ) (hlam : IsProbVec S lam) (a : D) (ha : a ∈ S) (i : ℕ) (hi : 1 ≤ i) :
    thresholdMeasure {t | Conflicts S lam t i a} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (Fintype.card D + i) * lam a) := by sorry

end MinCostMaj
