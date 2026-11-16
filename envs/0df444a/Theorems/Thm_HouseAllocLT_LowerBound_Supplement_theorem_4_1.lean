-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_theorem_4_1
-- name    : HouseAllocLT.LowerBound.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:22:27.772443+00:00
-- url     : https://prove2.me/theorems/d51eb375-38c8-46fe-8bc3-10cc79da9e17
-- title:
--   Theorem 4.1 — LT-RPG is exactly LT, mostly Pareto optimal, efficiently samplable and approximates within Uₙ < e/(e − 1)
-- statement:
--   For all $n,m\ge1$ and every deterministic maximum-matching routine, let $\mathrm{LT\text{-}RPG}=(1-\varepsilon_n)\mathrm{RPG}+\varepsilon_n\mathrm{RES}$ with $\varepsilon_n=1/(100D_n)$, $D_n=(n+2)!$. Then:
--
--   1. LT-RPG is exactly LT, with true and alternative reports ranging over all lists with ties, incomplete lists and empty lists;
--   2. for every profile, it returns a Pareto-optimal matching with probability at least $1-\varepsilon_n$;
--   3. it can be sampled exactly in expected polynomial time (for a polynomial-time routine);
--   4. its approximation ratio satisfies
--   $$\alpha_{n,m}(\mathrm{LT\text{-}RPG}_{\varepsilon_n})\le U_n:=\frac{100D_n}{(100D_n-1)\lambda_n}<\frac e{e-1};$$
--   5. the same bound holds for every rank-maximal prefix: $R_h^*(P)\le U_n\,X_h^{\mathrm{LT\text{-}RPG}}(P)$ whenever $R_h^*(P)>0$;
--   6. over all sizes, $\alpha(\mathrm{LT\text{-}RPG})\le e/(e-1)$;
--   7. for every $0<\varepsilon<1$ chosen independently of the reports, $\mathrm{LT\text{-}RPG}_\varepsilon$ is LT and has factor at most $1/[(1-\varepsilon)\lambda_n]$.
--
--   Together with Theorem 3.1 this shows that $e/(e-1)$ is the optimal uniform factor for LT mechanisms.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine (per size for clauses 1, 2, 4, 5, 7; one routine per size n, m for clauses 3 and 6); reason: the source states the result for whatever fixed routine the mechanism uses
--   - reading: "uses exact sampling in expected polynomial time" → for every polynomial-time routine family, a polynomial-time Las Vegas trial with fair coins whose success probability has polynomially bounded inverse and whose output, conditional on success, has law exactly LT-RPG(P); inputs coded with n, m and lengths in unary; reason: the source gives no machine model; this is the proof's construction (PDF p. 14, one uniform integer by rejection, then RPG with a polynomial-time routine [HK73]); a polynomial-time routine is the source's implicit assumption
--   - encoding: ε with 0 < ε < 1 chosen independently of the reports → an element ε of [0, 1] with 0 < ε < 1, a parameter that does not depend on the profile; reason: the same set of constants
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Theorem 4.1, display (10), PDF p. 10 (printed p. 8); Algorithm 2 and proof PDF pp. 13–14 (printed pp. 11–12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_LTRPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Theorem 4.1, PDF p. 10 (printed p. 8). For every `n, m ≥ 1` and every deterministic
maximum-matching routine: LT-RPG (`= (1 − ε_n) RPG + ε_n RES`, `ε_n = 1/(100 D_n)`) is exactly
LT on the full domain; it returns a Pareto-optimal matching with probability at least `1 − ε_n`;
`α_{n,m}(LT-RPG_{ε_n}) ≤ U_n < e/(e − 1)`; the same bound holds for every rank-maximal prefix;
and for every `0 < ε < 1` independent of the reports, `LT-RPG_ε` is LT with factor at most
`1/((1 − ε) λ_n)`. Over all sizes `α(LT-RPG) ≤ e/(e − 1)`. For polynomial-time routines it can be
sampled exactly in expected polynomial time. -/
theorem theorem_4_1 :
    (∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ MM : MaxMatchingRoutine n m,
      IsLT (ltrpg MM) ∧
      (∀ P : Profile n m, 1 - resProb n ≤ poProb (ltrpg MM) P) ∧
      approximationRatio (ltrpg MM) ≤ ENNReal.ofReal (upperFactor n) ∧
      upperFactor n < Real.exp 1 / (Real.exp 1 - 1) ∧
      (∀ (P : Profile n m) (h : ℕ), 0 < benchmarkPrefix P h →
        (benchmarkPrefix P h : ℝ) ≤ upperFactor n * expectedPrefix (ltrpg MM) P h) ∧
      (∀ ε : unitInterval, 0 < (ε : ℝ) → (ε : ℝ) < 1 →
        IsLT (ltrpgEps MM ε) ∧
        approximationRatio (ltrpgEps MM ε) ≤ ENNReal.ofReal (1 / ((1 - (ε : ℝ)) * lambdaN n)))) ∧
    (∀ MMs : ∀ n m : ℕ, MaxMatchingRoutine n m,
      uniformRatio (ltrpgFamily MMs) ≤ ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1))) ∧
    (∀ MMs : ∀ n m : ℕ, MaxMatchingRoutine n m,
      RoutinePolyTime MMs → IsExactLasVegasSampler (ltrpgFamily MMs)) := by sorry

end HouseAllocLT.LowerBound.Supplement
