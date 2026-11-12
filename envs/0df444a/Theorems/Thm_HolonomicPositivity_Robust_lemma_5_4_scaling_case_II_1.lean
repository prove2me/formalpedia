-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4_scaling_case_II_1
-- name    : HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:34:14.623082+00:00
-- url     : https://prove2.me/theorems/1b7b5111-56a8-4d2a-9aa2-b3b1af36a9f1
-- title:
--   Lemma 5.4, scaling in case II-1 — a scaling function S with S ≥ 0, B > 0, inequality (6) and C ≥ 0
-- statement:
--   Let $P, Q \in \mathbb{R}(x)$ and suppose $P$ has the Taylor expansion $P(x) = p_0 + p_1/x + p_2/x^2 + p_3/x^3 + O(x^{-4})$ at infinity (`HasTaylorExpansion`), $P(x) \ge -\tfrac13 - \tfrac{1}{9x^2} + O(x^{-3})$, $P(x) < 1 - \tfrac2x + O(x^{-2})$ (the first two clauses of condition (II) of Theorem 3.1), and the case hypothesis (II-1): $p_0 > -\tfrac13$ and $Q(x) \ge R_P(x) + O(x^{-3})$ with $R_P$ = `thresholdOne`. Then there is $S \in \mathbb{R}(x)$ with $S \ge 0$, such that $B(x) := 1 - S(x+2)$ is eventually positive, $A(x)/(B(x)B(x-1))$ satisfies inequality (6) with $A(x) := B(x)S(x+1) + P(x)$, and $C(x) := A(x)S(x) + Q(x) \ge 0$ eventually (`scaledB`, `scaledA`, `scaledC`, `SatisfiesInequalitySix`; $\ge$ and $>$ for rational functions mean for all sufficiently large $x$).
--
--   This is the part of the proof of Lemma 5.4 (Hagihara, pp. 13–14, STOC 2027 submission 328) that treats the case (II-1): $p_0 > -\tfrac13$ and $Q(x) \ge R_P(x) + O(x^{-3})$ with $R_P$ = `thresholdOne`; it is stated separately so that the proof of Lemma 5.4 can be split in three. The remaining clause of Lemma 5.4, the existence of $L$, follows from Lemma 5.3.
-- source:
--   Hagihara, F., Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission 328, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf (no DOI yet), pp. 13-14, proof of Lemma 5.4, case II-1

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

theorem lemma_5_4_scaling_case_II_1 (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ)
    (hT : HasTaylorExpansion P p₀ p₁ p₂ p₃)
    (hge : GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3))
    (hlt : LtMod (ev P) (fun x => 1 - 2 / x) (-2))
    (hp1 : -(1 / 3) < p₀)
    (hq : GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3)) :
    ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
      SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0) := by
  sorry

end HolonomicPositivity.Robust
