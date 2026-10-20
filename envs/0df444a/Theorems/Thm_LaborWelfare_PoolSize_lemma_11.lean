-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_lemma_11
-- name    : LaborWelfare.PoolSize.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:53.213163+00:00
-- url     : https://prove2.me/theorems/3bb2f6eb-4d57-480b-bbf2-a8710f362423
-- title:
--   Lemma 11, p. OA1 — existence and uniqueness of the positive demand–supply equilibrium (β = 1 case corrected)
-- statement:
--   Consider the base model with delay sensitivity $h>0$, a labor pool of size $N>0$, a price $p\ge 0$ and a wage $w\ge 0$.
--
--   1. If $w>0$ and $p<\bar v$, there is exactly one pair $(D,S)$ with $D>0$, $S>0$, $D<S$ satisfying the labor supply equation (2) and the demand equation (3) with delay (4) if and only if either $\beta>1$ or $p+2h/(wNE[1/a])<\bar v$.
--   2. If $w=0$ or $p\ge\bar v$, there is no such pair.
--   3. If $\beta=1$, $w>0$, $p<\bar v$, and $p+2h/(wNE[1/a])\ge\bar v$, there is no such pair.
--
--   $$w>0,\ p<\bar v\quad\Longrightarrow\quad\big(\exists!\,(D,S)\ \text{equilibrium}\big)\ \Longleftrightarrow\ \big(\beta>1\ \text{or}\ p+\tfrac{2h}{wNE[1/a]}<\bar v\big).$$
--
--   The corrected condition identifies exactly which positive-wage, sub-ceiling-price pairs have a positive market equilibrium; the platform's problem (7) optimizes over those feasible pairs.
--
--   **Formalization Note** The paper states clause 1 under $w>0$ and $p<\bar v$ alone. For $\beta=1$ that is not enough: writing $\rho=D/S$, the delay is $W=2/(wNE[1/a](1-\rho))$, which tends to $2/(wNE[1/a])>0$ as $\rho\to0^+$, so if $p+2h/(wNE[1/a])\ge\bar v$ no customer seeks service and no positive equilibrium exists. The extra disjunct is exactly the condition under which the paper's argument ($\lim_{\rho\to0^+}f(\rho)<0$) goes through; for $\beta>1$ it is not needed. The restriction $p\ge0$, $w\ge0$ is the domain of problem (7).
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), Lemma 11, p. OA1 (proof pp. OA1–OA2, displays (12)–(13)); existence clause corrected for β = 1

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Lemma 11, p. OA1 (base model `h > 0`), with the existence condition corrected for `β = 1`:
there the delay at utilization `ρ → 0⁺` tends to `2/(w N E[1/a])`, so a positive equilibrium exists
exactly when `p + 2h/(w N E[1/a]) < v̄`; for `β > 1` the page's hypotheses suffice. -/
theorem lemma_11 (M : Model) (hM : M.Std) (hh : 0 < M.h) (N p w : ℝ) (hN : 0 < N)
    (hp : 0 ≤ p) (hw : 0 ≤ w) :
    ((0 < w → p < M.vbar →
        (((∃! DS : ℝ × ℝ, IsMarketEq M N p w DS.1 DS.2) ↔
          (1 < M.beta ∨ p + 2 * M.h / (w * N * Einv M) < M.vbar)) ∧
         (M.beta = 1 → M.vbar ≤ p + 2 * M.h / (w * N * Einv M) →
           ∀ D S : ℝ, ¬ IsMarketEq M N p w D S))) ∧
      ((w = 0 ∨ M.vbar ≤ p) → ∀ D S : ℝ, ¬ IsMarketEq M N p w D S)) := by sorry

end LaborWelfare.PoolSize
