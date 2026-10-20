-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_lemma_13
-- name    : LaborWelfare.PoolSize.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:06.45925+00:00
-- url     : https://prove2.me/theorems/e48a1680-44e1-4c7a-baa5-41a65ab91574
-- title:
--   Lemma 13, p. OA4 — S* and D* increase in N; S* → ∞, D* → Λ/2 as N → ∞; S*, D*, ρ* → 0 as N ↓ N̲
-- statement:
--   In the base model ($h>0$), let $N\mapsto(p^*(N),w^*(N),D^*(N),S^*(N))$ select an optimal outcome for every $N>\underline N$. Then:
--
--   1. $S^*(N)$ and $D^*(N)$ are strictly increasing in $N$ on $(\underline N,\infty)$;
--   2. $\lim_{N\to\infty}S^*=\infty$ and $\lim_{N\to\infty}D^*=\Lambda/2$;
--   3. $\lim_{N\to\underline N^+}S^*=\lim_{N\to\underline N^+}D^*=\lim_{N\to\underline N^+}\rho^*=0$, where $\rho^*=D^*/S^*$.
--
--   $$S^*\uparrow\infty,\qquad D^*\uparrow\tfrac{\Lambda}{2},\qquad (S^*,D^*,\rho^*)\to 0\ \text{as}\ N\downarrow\underline N.$$
--
--   These limits supply the boundary behaviour from which the thresholds of Theorem 2 are obtained.
--
--   **Formalization Note** The optimum is a selection `opt : ℝ → Outcome` constrained to be optimal for every $N>\underline N$; by Lemma 1 it is unique there, so it is the paper's $(p^*,w^*,D^*,S^*)$. Its values for $N\le\underline N$ are unconstrained and never used.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), Lemma 13, p. OA4

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Lemma 13, p. OA4: `S*` and `D*` increase in `N`; `S* → ∞` and `D* → Λ/2` as `N → ∞`;
`S*`, `D*`, `ρ*` tend to `0` as `N ↓ N̲`. -/
theorem lemma_13 (M : Model) (hM : M.Std) (hh : 0 < M.h) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    StrictMonoOn (fun N => (opt N).S) (Set.Ioi (Nlow M)) ∧
      StrictMonoOn (fun N => (opt N).D) (Set.Ioi (Nlow M)) ∧
      Tendsto (fun N => (opt N).S) atTop atTop ∧
      Tendsto (fun N => (opt N).D) atTop (𝓝 (M.Lam / 2)) ∧
      Tendsto (fun N => (opt N).S) (𝓝[>] (Nlow M)) (𝓝 0) ∧
      Tendsto (fun N => (opt N).D) (𝓝[>] (Nlow M)) (𝓝 0) ∧
      Tendsto (fun N => util (opt N)) (𝓝[>] (Nlow M)) (𝓝 0) := by sorry

end LaborWelfare.PoolSize
