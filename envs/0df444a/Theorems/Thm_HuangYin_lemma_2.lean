-- Prove2me | Theorems.Thm_HuangYin_lemma_2
-- name    : HuangYin.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:22.945863+00:00
-- url     : https://prove2.me/theorems/401802fe-142e-4964-84ec-8ec92801f515
-- title:
--   Lemma 2 — optimal offering probabilities at $p_1=p_2=v_{HL}$ (corrected: $c_L\le v_{HL}$)
-- statement:
--   Assume $c_L\le v_{HL}$ and $\alpha<1$, and write $R=(v_{HL}-c_L)/(c_H-c_L)$. When $p_1=p_2=v_{HL}$, the following offering probabilities maximize the profit (2) over $(\xi_1,\xi_2)\in[0,1]^2$.
--
--   (i) If $0\le\alpha<(\sqrt{17}-3)/2$:
--
--   1. if $R<\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}$: $\xi_1=\frac{(2-\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)}$ and $\xi_2=\frac{(2-3\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)}$;
--   2. if $\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}\le R<\frac{2-\alpha}{1-\alpha}$: $\xi_1=1$ and $\xi_2=\frac{(1-\alpha)(v_{HL}-c_L)-\alpha(c_H-c_L)}{2(1-\alpha)(c_H-c_L)}$;
--   3. if $R\ge\frac{2-\alpha}{1-\alpha}$: $\xi_1=\xi_2=1$.
--
--   (ii) If $(\sqrt{17}-3)/2\le\alpha<1$:
--
--   1. if $R<\frac{2}{1+\alpha}$: $\xi_1=\frac{(1+\alpha)(v_{HL}-c_L)}{2(c_H-c_L)}$ and $\xi_2=0$;
--   2. if $\frac{2}{1+\alpha}\le R\le\frac{\alpha}{1-\alpha}$: $\xi_1=1$ and $\xi_2=0$;
--   3. if $\frac{\alpha}{1-\alpha}<R<\frac{2-\alpha}{1-\alpha}$: $\xi_1=1$ and $\xi_2=\frac{(1-\alpha)(v_{HL}-c_L)-\alpha(c_H-c_L)}{2(1-\alpha)(c_H-c_L)}$;
--   4. if $R\ge\frac{2-\alpha}{1-\alpha}$: $\xi_1=\xi_2=1$.
--
--   Lemma 2 gives the best offering probabilities in the case that Proposition 1 shows to be the optimal probabilistic selling policy.
--
--   Differences from the source:
--
--   - correction: no sign condition on vHL − cL → hypothesis cL ≤ vHL; reason: false as printed: α = 0, vH = 3, vL = 1, cH = 6, cL = 5 satisfy every assumption of the paper and give (vHL − cL)/(cH − cL) = −3, so the prescribed ξ1 = −3/2 lies outside [0, 1]; cL ≤ vHL is exactly the condition that the prescribed ξ1 is nonnegative, and it is implied by the vL ≥ cL that the paper's proof uses (p. 30)
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'the optimal product offering decisions are' / 'it is optimal to use' → the stated choice is feasible and attains the maximum (`OptimalOffer`, `IsOptimal`), not that it is the unique maximizer; reason: Proposition 1 (iii) calls both transparent policies optimal when vH − cH = vL − cL, so optimality cannot mean uniqueness
--   - reading: '(2−a)/(1−a)' in the last case of (i) and of (ii) → (2 − α)/(1 − α); reason: a typo: the lemma has no parameter a, and the preceding case of the same regime ends at (2 − α)/(1 − α)
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Lemma 2, p. 12

import Mathlib
import Definitions.Def_HuangYin_OptimalOffer
import Definitions.Def_HuangYin_vHL

namespace HuangYin

/-- **Lemma 2: optimal offering probabilities at `p1 = p2 = vHL`** (p. 12), corrected by the
hypothesis `cL ≤ vHL`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Lemma 2, p. 12.

Write `R = (vHL − cL)/(cH − cL)`. When `p1 = p2 = vHL` the following `(ξ1, ξ2)` maximize the
profit (2) over `[0,1]²`:

(i) `0 ≤ α < (√17 − 3)/2`:
* if `R < (4 − 4α − α²)/(2 − α − α²)`: `ξ1 = (2 − α − α²)(vHL − cL)/((4 − 4α − α²)(cH − cL))`,
  `ξ2 = (2 − 3α − α²)(vHL − cL)/((4 − 4α − α²)(cH − cL))`;
* if `(4 − 4α − α²)/(2 − α − α²) ≤ R < (2 − α)/(1 − α)`: `ξ1 = 1`,
  `ξ2 = ((1 − α)(vHL − cL) − α(cH − cL))/(2(1 − α)(cH − cL))`;
* if `R ≥ (2 − α)/(1 − α)`: `ξ1 = ξ2 = 1`.

(ii) `(√17 − 3)/2 ≤ α < 1`:
* if `R < 2/(1 + α)`: `ξ1 = (1 + α)(vHL − cL)/(2(cH − cL))`, `ξ2 = 0`;
* if `2/(1 + α) ≤ R ≤ α/(1 − α)`: `ξ1 = 1`, `ξ2 = 0`;
* if `α/(1 − α) < R < (2 − α)/(1 − α)`: `ξ1 = 1`,
  `ξ2 = ((1 − α)(vHL − cL) − α(cH − cL))/(2(1 − α)(cH − cL))`;
* if `R ≥ (2 − α)/(1 − α)`: `ξ1 = ξ2 = 1`.

**Formalization Note.** The hypothesis `cL ≤ vHL` is a correction: without it the first case of
(i) prescribes a negative `ξ1` (α = 0, vH = 3, vL = 1, cH = 6, cL = 5 gives `ξ1 = −3/2`).
The printed "(2−a)/(1−a)" is read as `(2 − α)/(1 − α)`. `α < 1` is the lemma's own range.
"Optimal" means attaining the maximum (`OptimalOffer`). -/
theorem lemma_2 (P : Params) (hcorr : P.cL ≤ vHL P) (hα : P.α < 1) :
    (P.α < (Real.sqrt 17 - 3) / 2 →
      (vHL P - P.cL) / (P.cH - P.cL) < (4 - 4 * P.α - P.α ^ 2) / (2 - P.α - P.α ^ 2) →
      OptimalOffer P (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))) ∧
    (P.α < (Real.sqrt 17 - 3) / 2 →
      (4 - 4 * P.α - P.α ^ 2) / (2 - P.α - P.α ^ 2) ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      (vHL P - P.cL) / (P.cH - P.cL) < (2 - P.α) / (1 - P.α) →
      OptimalOffer P (vHL P) (vHL P) 1
        (((1 - P.α) * (vHL P - P.cL) - P.α * (P.cH - P.cL)) / (2 * (1 - P.α) * (P.cH - P.cL)))) ∧
    (P.α < (Real.sqrt 17 - 3) / 2 →
      (2 - P.α) / (1 - P.α) ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      OptimalOffer P (vHL P) (vHL P) 1 1) ∧
    ((Real.sqrt 17 - 3) / 2 ≤ P.α →
      (vHL P - P.cL) / (P.cH - P.cL) < 2 / (1 + P.α) →
      OptimalOffer P (vHL P) (vHL P) ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
    ((Real.sqrt 17 - 3) / 2 ≤ P.α →
      2 / (1 + P.α) ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      (vHL P - P.cL) / (P.cH - P.cL) ≤ P.α / (1 - P.α) →
      OptimalOffer P (vHL P) (vHL P) 1 0) ∧
    ((Real.sqrt 17 - 3) / 2 ≤ P.α →
      P.α / (1 - P.α) < (vHL P - P.cL) / (P.cH - P.cL) →
      (vHL P - P.cL) / (P.cH - P.cL) < (2 - P.α) / (1 - P.α) →
      OptimalOffer P (vHL P) (vHL P) 1
        (((1 - P.α) * (vHL P - P.cL) - P.α * (P.cH - P.cL)) / (2 * (1 - P.α) * (P.cH - P.cL)))) ∧
    ((Real.sqrt 17 - 3) / 2 ≤ P.α →
      (2 - P.α) / (1 - P.α) ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      OptimalOffer P (vHL P) (vHL P) 1 1) := by sorry

end HuangYin
