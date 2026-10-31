-- Prove2me | Theorems.Thm_LevyExtrema_SBA_theorem_1
-- name    : LevyExtrema.SBA.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:09.010096+00:00
-- url     : https://prove2.me/theorems/a671ab58-63cd-47c1-b7a0-5429fa386691
-- title:
--   Theorem 1 — the law of the SBA error: $(Y_{L_n},\Delta_n,\delta_n)\overset d=(Y_{L_n},\overline Y_{L_n},\tau_{L_n}(Y))$ given $L_n$, with monotone bounds
-- statement:
--   Let $X$ be a Lévy process that is not compound Poisson with drift and let $(X,\ell,Y)$ be a stick-breaking coupling on $[0,T]$. For every $n\ge1$:
--
--   1. almost surely $\chi-\chi_n=(0,\Delta^{SB}_n,\delta^{SB}_n)$, where $\chi=(X_T,\overline X_T,\tau_T)$ and $\chi_n$ is the SBA (1.2);
--   2. conditionally on $L_n$,
--   $$(Y_{L_n},\Delta_n,\delta_n)\overset d=(Y_{L_n},\overline Y_{L_n},\tau_{L_n}(Y)),$$
--   and hence
--   $$(\Delta^{SB}_n,\delta^{SB}_n)\overset d=\big(\overline Y_{L_n}-Y^+_{L_n},\ \tau_{L_n}(Y)-L_n\mathbb 1_{\{Y_{L_n}>0\}}\big);$$
--   3. almost surely $0\le\Delta^{SB}_{n+1}\le\Delta^{SB}_n\le\Delta_n$, $0\le\delta_n\le L_n$ and $|\delta^{SB}_n|\le L_n$.
--
--   Since $L_n$ is independent of $Y$ and exponentially small in $n$, the theorem reduces the error of the SBA to the supremum of $Y$ over a short random interval; every $L^p$ bound of Theorem 2 rests on it.
--
--   Differences from the source:
--   - generalization: the coupling (X, ℓ, Y) constructed in Subsection 4.1 → any IsSBCoupling: Y with the triplet of X, V U(0,1)-iid, Y independent of V, (1.1) almost surely; reason: the proofs use only these properties, and the §4.1 coupling has them once Y, a random element of D[0,T] there, is continued after T by an independent copy, which changes nothing on [0,T] (exists_sbCoupling), so the source's statement is the instance of that coupling
--   - encoding: "conditionally on L_n, A =d B" → IdentDistrib of (L_n, A) and (L_n, B) (equality of the joint laws with L_n); reason: equality of the conditional laws given L_n is equality of the joint laws with L_n
--   - encoding: n ∈ N = {1, 2, …}; L_n a random time; V_1, V_2, … → 1 ≤ n; random times through Real.toNNReal; V indexed from 0; reason: notation only; L_n ∈ [0, T] almost surely
--   - encoding: X is not compound Poisson with drift → ¬ IsCPPWithDrift Tr, i.e. ¬(σ = 0 ∧ ν(ℝ) < ∞); reason: a Lévy process is compound Poisson with drift exactly when σ = 0 and ν is finite; same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Theorem 1, p. 3 (with (1.3)–(1.4)); proof in §4.2, p. 19

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_supTime
import Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
import Definitions.Def_LevyExtrema_SBA_StickBreaking
import Definitions.Def_LevyExtrema_SBA_IsSBCoupling
import Definitions.Def_LevyExtrema_SBA_SBAErrors

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Theorem 1 — the law of the error of the SBA.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Theorem 1, p. 3: "Assume the Lévy
process X is not compound Poisson with drift and let (X, ℓ, Y) be the coupling constructed in
Subsection 4.1 below, satisfying (1.1). For any n ∈ N, define the vector of errors of the SBA by
χ − χ_n = (0, Δ^SB_n, δ^SB_n) = (0, Δ_n − Y^+_{L_n}, δ_n − L_n · 1{Y_{L_n}>0}) … Then,
conditionally on L_n, (1.4) (Y_{L_n}, Δ_n, δ_n) =d (Y_{L_n}, Ȳ_{L_n}, τ_{L_n}(Y)), and hence
(Δ^SB_n, δ^SB_n) =d (Ȳ_{L_n} − Y^+_{L_n}, τ_{L_n}(Y) − L_n · 1{Y_{L_n}>0}). Moreover, the
inequalities 0 ≤ Δ^SB_{n+1} ≤ Δ^SB_n ≤ Δ_n, 0 ≤ δ_n ≤ L_n and |δ^SB_n| ≤ L_n hold a.s."

For every stick-breaking coupling with `X` not compound Poisson with drift and every `n ≥ 1`:
1. almost surely `χ − χ_n = (0, Δ^SB_n, δ^SB_n)`;
2. `(L_n, Y_{L_n}, Δ_n, δ_n)` and `(L_n, Y_{L_n}, Ȳ_{L_n}, τ_{L_n}(Y))` have the same law;
3. `(L_n, Δ^SB_n, δ^SB_n)` and `(L_n, Ȳ_{L_n} − Y^+_{L_n}, τ_{L_n}(Y) − L_n 1{Y_{L_n} > 0})` have
   the same law;
4. almost surely `0 ≤ Δ^SB_{n+1} ≤ Δ^SB_n ≤ Δ_n`, `0 ≤ δ_n ≤ L_n` and `|δ^SB_n| ≤ L_n`.

**Formalization Note.** The coupling of §4.1 is any `IsSBCoupling` (its existence is
`exists_sbCoupling`). "Conditionally on L_n, A =d B" is encoded as equality of the joint laws of
`(L_n, A)` and `(L_n, B)`. Random times enter through `Real.toNNReal`. `n ≥ 1` (N = {1, 2, …}). -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (Tr : Triplet) (T : ℝ≥0)
    (hcoup : IsSBCoupling P X Y V Tr T) (hcpp : ¬ IsCPPWithDrift Tr) (n : ℕ) (hn : 1 ≤ n) :
    (∀ᵐ ω ∂P, (X T ω, runSup (fun s => X s ω) T, ((supTime (fun s => X s ω) T : ℝ≥0) : ℝ))
        - sba T Y V n ω = (0, errSupSB T X Y V n ω, errTimeSB T X Y V n ω)) ∧
    IdentDistrib
      (fun ω => (stickRem T V n ω, atStick T Y V n ω, errSup T X Y V n ω, errTime T X Y V n ω))
      (fun ω => (stickRem T V n ω, atStick T Y V n ω,
        runSup (fun s => Y s ω) (Real.toNNReal (stickRem T V n ω)),
        ((supTime (fun s => Y s ω) (Real.toNNReal (stickRem T V n ω)) : ℝ≥0) : ℝ))) P P ∧
    IdentDistrib
      (fun ω => (stickRem T V n ω, errSupSB T X Y V n ω, errTimeSB T X Y V n ω))
      (fun ω => (stickRem T V n ω,
        runSup (fun s => Y s ω) (Real.toNNReal (stickRem T V n ω)) - max (atStick T Y V n ω) 0,
        ((supTime (fun s => Y s ω) (Real.toNNReal (stickRem T V n ω)) : ℝ≥0) : ℝ)
          - (if 0 < atStick T Y V n ω then stickRem T V n ω else 0))) P P ∧
    (∀ᵐ ω ∂P, 0 ≤ errSupSB T X Y V (n + 1) ω ∧
      errSupSB T X Y V (n + 1) ω ≤ errSupSB T X Y V n ω ∧
      errSupSB T X Y V n ω ≤ errSup T X Y V n ω ∧
      0 ≤ errTime T X Y V n ω ∧ errTime T X Y V n ω ≤ stickRem T V n ω ∧
      |errTimeSB T X Y V n ω| ≤ stickRem T V n ω) := by sorry

end LevyExtrema.SBA
