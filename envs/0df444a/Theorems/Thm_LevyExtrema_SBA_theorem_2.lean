-- Prove2me | Theorems.Thm_LevyExtrema_SBA_theorem_2
-- name    : LevyExtrema.SBA.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:58.825699+00:00
-- url     : https://prove2.me/theorems/40bded1d-5efa-4dae-896c-51487a87cb10
-- title:
--   Theorem 2 with (4.24) — the SBA errors decay geometrically in $L^p$ at rate $\eta_p\in[3/2,2]$ (corrected: β+ = δ when β = 0)
-- statement:
--   Let $X$ be a Lévy process with generating triplet $(\sigma^2,\nu,b)$ that is not compound Poisson with drift, let $(X,\ell,Y)$ be a stick-breaking coupling on $[0,T]$, and let $p\ge1$. Then:
--
--   1. **(a)** for every $n\ge1$,
--   $$\max\big\{\mathbb E\big[|\delta^{SB}_n|^p\big],\ \mathbb E\big[\delta_n^p\big]\big\}\le T^p(1+p)^{-n};$$
--   2. **(b0)** for every admissible $\delta$, the rate $\eta_p$ of (4.22) lies in $[3/2,2]$;
--   3. **(b1)** if $\min\{I^p_+,I^p_-\}<\infty$, then for every admissible $\delta$, $\mathbb E[(\Delta^{SB}_n)^p]=\mathcal O(\eta_p^{-n})$: there is $C_0>0$ with $\mathbb E[(\Delta^{SB}_n)^p]\le C_0\eta_p^{-n}$ for all $n\ge1$;
--   4. **(b2)** if $I^p_+<\infty$, then for every admissible $\delta$, $\mathbb E[\Delta_n^p]=\mathcal O(\eta_p^{-n})$ in the same sense;
--   5. **(b3)** the constants are explicit (4.24): for every admissible $\delta$ with $\alpha_+<p$ whenever $\alpha<p$, and every $n\ge1$,
--   $$\mathbb E[\Delta_n^p]\le C_p(X)\,T^{\eta_p-1}\eta_p^{-n}\ \text{ if }I^p_+<\infty,\qquad \mathbb E[(\Delta^{SB}_n)^p]\le C^*_p(X)\,T^{\eta_p-1}\eta_p^{-n}\ \text{ if }\min\{I^p_+,I^p_-\}<\infty,$$
--   with $C_p(X)$, $C^*_p(X)$ as in (4.23).
--
--   The strong error of the stick-breaking approximation of the supremum and its time therefore decays geometrically in the number $n$ of sticks, at a rate $\eta_p\ge3/2$ for every Lévy process, with constants computable from the characteristics of $X$. This is what makes the SBA an efficient Monte Carlo and multilevel Monte Carlo scheme.
--
--   Differences from the source:
--   - correction: β₊ = β + δ·1{I^β_0 = ∞} (4.6) → β₊ = β + δ when I^β_0 = ∞ or β = 0 (betaPlus); reason: as printed, standard Brownian motion (σ = 1, ν = 0, b = 0) satisfies every assumption and has β = 0, I^0_0 = 0 < ∞, hence β₊ = 0, and p/β₊ in (4.12), (4.13), (4.23) is undefined; with δ ∈ (0,1) the formulas are defined, the proofs use only I^{β₊}_0 < ∞, β₊ ≤ 2 and β₊ ≤ 1 when I^1_0 < ∞, and α₊, η_p are unchanged
--   - reading: "can thus pick δ ∈ (0, 2 − β), satisfying β + δ < 1 whenever β < 1" (one chosen δ) → the statement holds for every admissible δ (AdmissibleDelta Tr δ); reason: the stronger of the two readings of "pick δ"; it implies the statement for the chosen δ
--   - reading: (4.24) for the δ picked in the proof of Corollary 3 ("we may assume that p > α₊") → clause (b3) for every admissible δ with α < p → α₊ < p; reason: the proof chooses δ with this property; such δ always exist, and for p > α the rate η_p = 2 does not depend on δ, so the O-form clauses (b1), (b2) carry no restriction
--   - generalization: the coupling (X, ℓ, Y) constructed in Subsection 4.1 → any IsSBCoupling: Y with the triplet of X, V U(0,1)-iid, Y independent of V, (1.1) almost surely; reason: the proofs use only these properties, and the §4.1 coupling has them once Y, a random element of D[0,T] there, is continued after T by an independent copy, which changes nothing on [0,T] (exists_sbCoupling), so the source's statement is the instance of that coupling
--   - encoding: f(n) = O(g(n)) as n → ∞ (Appendix A.1) → ∃ C₀ > 0, ∀ n ≥ 1, f(n) ≤ C₀ g(n); reason: Appendix A.1: "f(n) being bounded above by C_0 g(n) for some constant C_0 > 0 and all n ∈ N"
--   - encoding: max{E[|δ^SB_n|^p], E[δ^p_n]} ≤ T^p(1+p)^{−n}; "the constants … are explicit (see (4.24))" → two separate bounds in (a); clause (b3) with CpX and CpStar; reason: same content
--   - encoding: E[Z] for a nonnegative random variable Z, and bounds E[Z] ≤ c → ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal c; reason: lintegral of a nonnegative variable is its expectation (possibly ∞), so no bound holds by a junk value
--   - encoding: X is not compound Poisson with drift → ¬ IsCPPWithDrift Tr, i.e. ¬(σ = 0 ∧ ν(ℝ) < ∞); reason: a Lévy process is compound Poisson with drift exactly when σ = 0 and ν is finite; same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Theorem 2, p. 6; (4.24), proof of Theorem 2, p. 25; O-notation, Appendix A.1, p. 30

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
import Definitions.Def_LevyExtrema_SBA_IsSBCoupling
import Definitions.Def_LevyExtrema_SBA_SBAErrors
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_betaPlus
import Definitions.Def_LevyExtrema_SBA_alpha
import Definitions.Def_LevyExtrema_SBA_eta
import Definitions.Def_LevyExtrema_SBA_Constants

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Theorem 2 with (4.24) — the SBA errors decay geometrically in L^p at rate η_p ∈ [3/2, 2].**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Theorem 2, p. 6: "Under the
assumptions of Theorem 1, the following holds for any p ≥ 1. (a) The inequality
max{E[|δ^SB_n|^p], E[δ^p_n]} ≤ T^p(1 + p)^{−n} holds for any n ∈ N. (b) If min{I^p_+, I^p_−} < ∞
(resp. I^p_+ < ∞), then E[(Δ^SB_n)^p] (resp. E[Δ^p_n]) is bounded above by O(η_p^{−n}) as n → ∞,
where η_p lies in the interval [3/2, 2] for any Lévy process X. Both η_p, defined in (4.22), and
the constants in O(η_p^{−n}) are explicit in the characteristics (σ², ν, b) of X (see (4.24))."
and (4.24), p. 25: "E[Δ^p_n] ≤ C_p(X)T^{η_p−1}η_p^{−n} (resp. E[(Δ^SB_n)^p] ≤
C*_p(X)T^{η_p−1}η_p^{−n}), where C_p(X) (resp. C*_p(X)) is as in (4.23) in Corollary 3."

For every stick-breaking coupling `(X, ℓ, Y)` on `[0, T]` with `X` not compound Poisson with drift
and every `p ≥ 1`:
(a) `E[|δ^SB_n|^p] ≤ T^p(1+p)^{−n}` and `E[δ_n^p] ≤ T^p(1+p)^{−n}` for all `n ≥ 1`;
(b0) `η_p ∈ [3/2, 2]` for every admissible δ;
(b1) if `min{I^p_+, I^p_−} < ∞`, for every admissible δ, `E[(Δ^SB_n)^p] = O(η_p^{−n})`;
(b2) if `I^p_+ < ∞`, for every admissible δ, `E[Δ_n^p] = O(η_p^{−n})`;
(b3) (4.24): for every admissible δ with `α < p → α₊ < p`, `E[Δ_n^p] ≤ C_p(X)T^{η_p−1}η_p^{−n}`
when `I^p_+ < ∞`, and `E[(Δ^SB_n)^p] ≤ C*_p(X)T^{η_p−1}η_p^{−n}` when `min{I^p_+, I^p_−} < ∞`.

**Formalization Note.** β₊ is corrected (`betaPlus`: β₊ = δ also when β = 0); every statement is
for every admissible δ. O(·) is Appendix A.1's: bounded by `C₀ g(n)` for some `C₀ > 0` and all
`n ∈ N = {1, 2, …}`. Expectations are lintegrals of `ofReal`; powers with exponent `−n` are
`Real.rpow`. The hypothesis `α < p → α₊ < p` of (b3) is the proof's "we may assume p > α₊". -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (Tr : Triplet) (T : ℝ≥0)
    (hcoup : IsSBCoupling P X Y V Tr T) (hcpp : ¬ IsCPPWithDrift Tr) (p : ℝ) (hp : 1 ≤ p) :
    -- (a)
    (∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, ENNReal.ofReal (|errTimeSB T X Y V n ω| ^ p) ∂P
          ≤ ENNReal.ofReal ((T : ℝ) ^ p * (1 + p) ^ (-(n : ℝ))) ∧
      ∫⁻ ω, ENNReal.ofReal (errTime T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal ((T : ℝ) ^ p * (1 + p) ^ (-(n : ℝ)))) ∧
    -- (b0) η_p ∈ [3/2, 2]
    (∀ δ : ℝ, AdmissibleDelta Tr δ → 3 / 2 ≤ eta Tr δ p ∧ eta Tr δ p ≤ 2) ∧
    -- (b1) O-form for Δ^SB_n
    (min (Iplus Tr p) (Iminus Tr p) < ⊤ → ∀ δ : ℝ, AdmissibleDelta Tr δ →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSupSB T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (C₀ * eta Tr δ p ^ (-(n : ℝ)))) ∧
    -- (b2) O-form for Δ_n
    (Iplus Tr p < ⊤ → ∀ δ : ℝ, AdmissibleDelta Tr δ →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSup T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (C₀ * eta Tr δ p ^ (-(n : ℝ)))) ∧
    -- (b3) = (4.24), explicit constants
    (∀ δ : ℝ, AdmissibleDelta Tr δ → (alpha Tr < p → alphaPlus Tr δ < p) →
      (Iplus Tr p < ⊤ → ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSup T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (CpX Tr T δ p * (T : ℝ) ^ (eta Tr δ p - 1)
              * eta Tr δ p ^ (-(n : ℝ)))) ∧
      (min (Iplus Tr p) (Iminus Tr p) < ⊤ → ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSupSB T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (CpStar Tr T δ p * (T : ℝ) ^ (eta Tr δ p - 1)
              * eta Tr δ p ^ (-(n : ℝ))))) := by sorry

end LevyExtrema.SBA
