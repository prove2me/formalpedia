-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_B_11
-- name    : OnlineBinCover.lemma_B_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:22.974572+00:00
-- url     : https://prove2.me/theorems/9991d74e-c0a0-483c-9793-249873e64f2e
-- title:
--   Lemma B.11 — $\mathrm{ALG}_{BP}(I)\ge(1-8\varepsilon)\mathrm{OPT}(I)-O(K\mathrm{vol}(I)^{5/6}+K/p)$
-- statement:
--   For every constant $C_3>0$ (the constant of Lemma 3.3) there is $C>0$ such that the following holds. Let $0<\varepsilon<1/8$, $K=\lceil\varepsilon^{-2}\rceil$, $0<p\le1$, let $I$ have sizes in $(0,1]$, and let $J$ be a set of items with
--
--   $$\mathrm{OPT}(J)\ge(1-4\varepsilon)\,p\,\mathrm{OPT}(I)-C_3\big(pK\mathrm{vol}(I)^{5/6}+K\big)$$
--
--   (the complement of the failure event of Lemma 3.3). Then for every LP solution $x$ on $J$ meeting the guarantee of Lemma 2.2, the blueprint has
--
--   $$\mathrm{ALG}_{BP}(I)\ge(1-8\varepsilon)\,\mathrm{OPT}(I)-C\Big(K\mathrm{vol}(I)^{5/6}+\frac Kp\Big).$$
--
--   The blueprint built from a sample is thus almost as large as the optimum of the whole instance.
--
--   Differences from the source:
--   - encoding: "Outside the failure event in Lemma 3.3" → for every constant $C_3>0$ there is $C$ such that the bound holds whenever $J$ satisfies the conclusion of Lemma 3.3 with constant $C_3$; reason: the complement of that failure event, with its constant
--   - generalization: the uniform sample $I_p$ of size $\lfloor pn\rfloor$ and the LP solution of the algorithm → every item set $J$ and every LP solution meeting Lemma 2.2 on $J$; reason: the argument is deterministic and uses only that guarantee; specializes to the sample
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
--   - reading: the sampling fraction $p$ (Algorithm 2's input; $I_p$ has $\lfloor pn\rfloor$ items of $I$) → $0<p\le1$; reason: a sampling fraction of the input; this is the range the paper uses (App. B.6 takes $p<1$)
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.11, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Lemma B.11, p.25. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

"Outside the failure event in Lemma 3.3": for every constant `C₃ > 0` (the constant of Lemma 3.3)
there is `C > 0` such that, for every `ε ∈ (0, 1/8)`, `p ∈ (0, 1]`, every instance with sizes in
`(0, 1]` and every sample `J` with `OPT(J) ≥ (1 − 4ε) p OPT(I) − C₃ (p K vol(I)^{5/6} + K)`, every
blueprint built from an LP solution meeting Lemma 2.2 on `J` has
`ALGBP(I) ≥ (1 − 8ε) OPT(I) − C (K vol(I)^{5/6} + K/p)`. -/
theorem lemma_B_11 : ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → ∀ (J : Finset (Fin n)) (ε p : ℝ),
      0 < ε → ε < 1 / 8 → 0 < p → p ≤ 1 →
      (1 - 4 * ε) * p * (OPT s : ℝ) -
          C₃ * (p * (Kof ε : ℝ) * vol s ^ ((5 : ℝ) / 6) + (Kof ε : ℝ)) ≤ (OPTon s J : ℝ) →
      ∀ x : (Fin (Kof ε) → ℕ) →₀ ℝ, LPSpec s J ε x →
        (1 - 8 * ε) * (OPT s : ℝ) - C * ((Kof ε : ℝ) * vol s ^ ((5 : ℝ) / 6) + (Kof ε : ℝ) / p) ≤
          (ALGBP x p : ℝ) := by sorry

end OnlineBinCover
