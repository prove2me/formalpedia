-- Prove2me | Theorems.Thm_MinFracProphet_theorem_2_lower_bound_long_shot
-- name    : MinFracProphet.theorem_2_lower_bound_long_shot
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:33.601627+00:00
-- url     : https://prove2.me/theorems/b6f07012-fced-4172-8305-47a4452ea254
-- title:
--   Proof of Theorem 2 (lower bound), p.23: on long-shot sellers the optimal policy buys in-house and the ratio tends to $(1+\frac{n-1}{\ell^{1/(p-1)}})^{p-1}$
-- statement:
--   Let $n\ge1$, $p>1$, $q=-\frac1{p-1}$ and $0<\ell<1$. For $0<\varepsilon<1$ and $u>\ell$, consider the long-shot instance: seller $1$ is in-house at price $1$, and each other seller has price $\ell$ with probability $1-\varepsilon$ and $u$ with probability $\varepsilon$. Let $\mathbb E[b_i]$ be the means of the dynamic program of Lemma 8, so that $\mathbb E[\mathrm{ALG}^{\mathrm{DP}}(C,p)]=\mathbb E[b_1]$. Then:
--
--   1. for every $\varepsilon\in(0,1)$ and every external seller $i\in\{2,\dots,n\}$, $\mathbb E[b_i]\to\infty$ as $u\to\infty$;
--   2. for every $\varepsilon\in(0,1)$, $\mathbb E[\mathrm{ALG}^{\mathrm{DP}}(C,p)]=\mathbb E[b_1]\to1$ as $u\to\infty$;
--   3. $\mathbb E[\mathrm{OPT}(C,p)]\to\bigl(1+(n-1)\ell^q\bigr)^{1/q}$ as $\varepsilon\to0^+$ and $u\to\infty$ jointly;
--   4. letting first $u\to\infty$ and then $\varepsilon\to0^+$,
--   $$
--   \frac{\mathbb E[\mathrm{ALG}^{\mathrm{DP}}(C,p)]}{\mathbb E[\mathrm{OPT}(C,p)]}\ \longrightarrow\ \Bigl(1+\frac{n-1}{\ell^{1/(p-1)}}\Bigr)^{p-1}.
--   $$
--
--   Since DP is optimal, no policy beats this ratio on these instances, which is the lower bound of Theorem 2.
--
--   **Formalization Note** Sellers and stages are 0-based in Lean: seller `0` is in-house, `dpBeta p ν 0` is $\mathbb E[b_1]$. $\mathbb E[\mathrm{OPT}]$ is a lower Lebesgue integral in $[0,\infty]$ (it lies in $(0,1]$ here); clause 4 divides by its real value and is written with explicit $\eta$, $\varepsilon_0$, $U$.
--
--   Differences from the source:
--   - reading: Ci = ℓ w.p. 1−ε and Ci = u w.p. ε for all i ∈ {1,…,n} → sellers 2,…,n (Lean 1,…,n−1) are long shots; seller 1 is the in-house point mass at 1; reason: D_1 is fixed to P[C_1 = 1] = 1 in the in-house problem
--   - reading: E[b_{n−1}] = E[c_{n−1}] → ∞, E[ALG^DP(C,p)] = 1, and inf_π E[ALG^DP]/E[OPT] = (3) “for ε → 0” → limits: E[b_i] → ∞ and E[b_1] → 1 as u → ∞ for each ε, and the ratio tends to (3) as u → ∞ and then ε → 0⁺; reason: at finite u these equalities are false (b_{n−1} < c_{n−1}, E[ALG^DP] < 1); the page argues in the limit u → ∞
--   - reading: E[b_i] → ∞ inductively for all i → E[b_i] → ∞ for the external sellers i = 2,…,n (Lean 1,…,n−1); reason: E[b_1] is the in-house stage and tends to 1, as the page’s next sentence E[ALG^DP] = 1 says
--   - generalization: E[OPT(C,p)] computed for ε → 0 → E[OPT] → (1+(n−1)ℓ^q)^{1/q} jointly as ε → 0⁺ and u → ∞; reason: joint convergence implies the limit as ε → 0 along any u → ∞, in particular the iterated one the page uses
--   - encoding: E[ALG^DP(C,p)] → dpBeta p ν 0 = E[b_1]; reason: E[ALG^DP] = E[J_1(0,C_1)] = E[b_1] by the DP optimality milestone and Lemma 8
--   - reading: ℓ < 1 (positivity of ℓ not written) → 0 < ℓ < 1; reason: prices are non-negative (§1.2) and (3) divides by ℓ^{1/(p−1)}, so ℓ > 0 is implicit; for ℓ ≤ 0 the formula is undefined
--   - encoding: sellers 1,…,n, seller 1 in-house (P[C_1 = 1] = 1) → sellers Fin n with 0 < n, seller 0 in-house (law dirac 1); reason: Lean convention; n counts the in-house seller and n = 0 has no feasible allocation
--   - encoding: stages i = 1,…,n → stages i = 0,…,n−1 (Lean stage i is the paper’s stage i+1), law ν ⟨i,_⟩; reason: Lean convention, a shift of the index
--   - encoding: E[OPT(C,p)] and the ratio → EOPT in ℝ≥0∞ (lintegral), its toReal in the ratio; reason: E[OPT] ∈ (0,1] on these instances, so toReal is exact
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), proof of Theorem 2 (lower bound), p.23

import Mathlib
import Definitions.Def_MinFracProphet_Model
import Definitions.Def_MinFracProphet_DynamicProgram

open MeasureTheory Filter Topology

namespace MinFracProphet

/-- **Proof of Theorem 2 (lower bound)**, p.23 of J. Qin, S. Vardi, A. Wierman, *Minimization
Fractional Prophet Inequalities for Sequential Procurement*, author manuscript
(sha256 672fa87c…79125d3).

Let `n ≥ 1`, `p > 1`, `q = -1/(p-1)`, `0 < ℓ < 1`, and consider the long-shot instance: seller 1
in-house at price `1`, every other seller at price `ℓ` with probability `1-ε` and `u` with
probability `ε`. With `E[b_i]` the means of the dynamic program of Lemma 8:

1. for every `ε ∈ (0,1)` and every external seller `i`, `E[b_i] → ∞` as `u → ∞`;
2. for every `ε ∈ (0,1)`, `E[ALG^DP(C,p)] = E[b_1] → 1` as `u → ∞`;
3. `E[OPT(C,p)] → (1 + (n-1) ℓ^q)^{1/q}` as `ε → 0⁺` and `u → ∞` (jointly);
4. the ratio `E[ALG^DP(C,p)] / E[OPT(C,p)]` tends to `(1 + (n-1)/ℓ^{1/(p-1)})^{p-1}` when first
   `u → ∞` and then `ε → 0⁺`.

**Formalization Note** Stages and sellers are 0-based: seller `0` is the in-house seller and the
external sellers are `1, …, n-1`; `dpBeta p ν 0 = E[b_1]` is `E[ALG^DP]` by Lemma 8 and the DP
optimality milestone. The page's long-shot instance is printed "for all `i ∈ {1,…,n}`"; seller 1
is the in-house point mass (R11). The page's "E[ALG^DP] = 1", "E[b_{n-1}] = E[c_{n-1}]" and the
final "inf_π … =" are limits (R11); clause 4 is the iterated limit, written with `η`, `ε₀`, `U`.
Clause 3 is stated jointly in `(ε, u)`, which implies the page's limit for `ε → 0` along any
`u → ∞`. `E[OPT]` is a lower Lebesgue integral in `ℝ≥0∞`; it lies in `(0,1]` here. -/
theorem theorem_2_lower_bound_long_shot (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (q : ℝ)
    (hq : q = -1 / (p - 1)) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ i : ℕ, 1 ≤ i → i < n →
        Tendsto (fun u => dpBeta p (longShot n ℓ u ε) i) atTop atTop) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        Tendsto (fun u => dpBeta p (longShot n ℓ u ε) 0) atTop (𝓝 1)) ∧
      Tendsto (fun z : ℝ × ℝ => EOPT p (longShot n ℓ z.2 z.1)) (𝓝[>] 0 ×ˢ atTop)
        (𝓝 (ENNReal.ofReal ((1 + ((n : ℝ) - 1) * ℓ ^ q) ^ (1 / q)))) ∧
      (∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ U : ℝ, ∀ u : ℝ, U ≤ u →
        |dpBeta p (longShot n ℓ u ε) 0 / (EOPT p (longShot n ℓ u ε)).toReal -
            (1 + ((n : ℝ) - 1) / ℓ ^ (1 / (p - 1))) ^ (p - 1)| < η) := by sorry

end MinFracProphet
