-- Prove2me | Theorems.Thm_MinCostMaj_lemma_tail_bound
-- name    : MinCostMaj.lemma_tail_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:13:29.355262+00:00
-- url     : https://prove2.me/theorems/8204c609-8334-405a-abde-18592f9049f7
-- title:
--   Lemma "Tail bound" — $\Pr[L(v)=i]\le C\,2^{-i}$
-- statement:
--   There is a constant $C=C(\mathbf A)$ such that for every variable $v$ (potato $A^J_v$, LP marginals $\lambda_v$) and every $i\ge1$,
--   $$\Pr\big[L(v)=i\big]\le C\,2^{-i},$$
--   the probability being over the random threshold sequence.
--
--   The geometric tail of the levels is what keeps the expected cost of the rounding within a constant factor of the LP value.
--
--   Differences from the source:
--   - encoding: C = C(A) → for every domain size d, a constant C chosen before the potato, the marginals and i; reason: the statement involves only the domain of A, so a constant depending on |A| is a constant depending on A
--   - encoding: LP marginal λ_v → any probability vector on A^J_v; reason: the BLP marginals are such vectors
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Tail bound", p.21 (PDF p.22)

import Mathlib
import Definitions.Def_MinCostMaj_Levels
import Definitions.Def_MinCostMaj_thresholdLaw

namespace MinCostMaj

/-- **Lemma "Tail bound"**, p.21 (PDF p.22).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Lemma "Tail bound", p.21: "There is a constant C = C(A) such that, for every variable v and
every i ≥ 1, Pr[L(v) = i] ≤ C2^{−i}."

For every domain size `d = |A|` there is `C` such that for every potato `S ⊆ Fin d`, every
probability vector `λᵥ` on it and every `i ≥ 1`, the probability under the threshold law that the
level procedure returns `L(v) = i` is at most `C · 2^{−i}`.

**Formalization Note.** `C` is chosen before `S`, `λᵥ` and `i` and depends only on `|A|` (the
statement involves no relation of `A`). -/
theorem lemma_tail_bound :
    ∀ d : ℕ, ∃ C : ℝ, ∀ (S : Finset (Fin d)) (lam : Fin d → ℝ), IsProbVec S lam →
      ∀ i : ℕ, 1 ≤ i →
        thresholdMeasure {t | level S lam t = i} ≤ ENNReal.ofReal (C * ((1 : ℝ) / 2) ^ i) := by sorry

end MinCostMaj
