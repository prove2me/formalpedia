-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_4_2
-- name    : NewtonLCP.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:19:05.40165+00:00
-- url     : https://prove2.me/theorems/d9d064d5-ba3c-49c2-9c2e-865bf6cb5dde
-- title:
--   Theorem 4.2 (corrected: $O$-bound rounded up) — Algorithm 1 uses $O(\sqrt n(1+\kappa)\log(\mu_0/\mu_1))$ solves and stays in $N^2(\beta)$
-- statement:
--   Let $M\in P_\star(\kappa)$ and $q\in\mathbb R^n$ with $n\ge1$, and choose
--
--   $$\beta\in\Big[\frac{1}{8(1+\kappa)},\frac{1}{4(1+\kappa)}\Big],\qquad \delta\in\Big[\frac{1}{32\sqrt n(1+\kappa)},\frac{1}{16\sqrt n(1+\kappa)}\Big].$$
--
--   For every starting point $(x^0,s^0,\mu^0)\in N^2(\beta)$ and every target $\mu_1>0$, Algorithm 1 returns $(x_{\mathrm{out}},s_{\mathrm{out}},\mu_{\mathrm{out}})$ with
--
--   1. $(x_{\mathrm{out}},s_{\mathrm{out}},\mu_{\mathrm{out}})\in N^2(\beta)$ (in particular $(x_{\mathrm{out}},s_{\mathrm{out}})\in\mathcal F_{>0}(M,q)$ and $\mu_{\mathrm{out}}>0$);
--   2. $\mu_{\mathrm{out}}\le\mu_1$;
--   3. the number of linear system solves is at most $\big\lceil C\sqrt n(1+\kappa)\log(\mu^0/\mu_1)\big\rceil_+$,
--
--   where $C>0$ is an absolute constant, independent of $n$, $\kappa$, $M$, $q$, $\beta$, $\delta$, the start and $\mu_1$.
--
--   This is the simple analysis of the standard path-following IPM, with linear dependence on $1+\kappa$.
--
--   **Formalization Note** $M\in P_\star(\kappa)$ is the published `IsPStarK M κ`; the solve count is the counter of `algorithm1` (one solve per iteration).
--
--   Differences from the source:
--   - correction: "$O(\sqrt n(1+\kappa)\log(\mu_0/\mu_1))$ linear system solves" → at most $\lceil C\sqrt n(1+\kappa)\log(\mu^0/\mu_1)\rceil_+$ solves; reason: the literal bound $C\sqrt n(1+\kappa)\log(\mu^0/\mu_1)$ is false for $\mu_1$ just below $\mu^0$: $n=1$, $M=(1)$, $q=0$, $(x^0,s^0,\mu^0)=(1,1,1)$, $\mu_1=e^{-t}$ satisfies every hypothesis and uses one solve, while $Ct<1$ for $t<1/C$.
--   - reading: "a suitable starting point $(x^0,s^0,\mu^0)\in N^2(\beta)$" → every point of $N^2(\beta)$; reason: the proof uses nothing else, and Theorem 5.1's wording ("Given an initial point") confirms it.
--   - encoding: $n$ arbitrary → $n\ge1$; reason: the printed range of $\delta$ divides by $\sqrt n$ and is undefined at $n=0$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 4.2, p.13 (proof p.14)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Centrality
import Definitions.Def_NewtonLCP_Supplement_Algorithm1

universe u

namespace NewtonLCP.Supplement

/-- **Theorem 4.2** (Algorithm 1, linear dependence on `1 + κ`). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 4.2, p.13 (proof p.14, via Lemma 4.4).

If `M ∈ P⋆(κ)`, for the choice `β ∈ [1/(8(1+κ)), 1/(4(1+κ))]`,
`δ ∈ [1/(32√n(1+κ)), 1/(16√n(1+κ))]`, and a starting point `(x⁰, s⁰, µ⁰) ∈ N²(β)`, Algorithm 1
finds a feasible solution `(x_out, s_out, µ_out) ∈ N²(β)` with `µ_out ≤ µ₁` in time dominated by
`O(√n(1+κ) log(µ⁰/µ₁))` linear system solves.

**Formalization Note.**
* `n = Fintype.card ι ≥ 1` (`[Nonempty ι]`): the printed range of `δ` divides by `√n`.
* "`M ∈ P⋆(κ)`" is the published `IsPStarK M κ` (so `κ ≥ κ̂(M) ≥ 0`); `κ` in the ranges and the
  bound is this parameter, not `κ̂(M)`. The ranges are the closed printed intervals.
* "A suitable starting point" is read as *every* point of `N²(β)` (the proof uses nothing else).
* "Time dominated by `k` linear system solves" is "at most `k` Newton-system solves", counted by
  the solve counter of `algorithm1` (one per iteration).
* **Correction of the `O`-bound.** Read literally, "`solves ≤ C·√n(1+κ)·log(µ⁰/µ₁)`" is false
  for `µ₁` just below `µ⁰`: `n = 1`, `M = (1)`, `q = 0`, `(x⁰, s⁰, µ⁰) = (1, 1, 1)`,
  `µ₁ = e^{−t}` uses one solve while `C·t < 1` for small `t`. The bound is stated as
  `solves ≤ ⌈C·√n(1+κ)·log(µ⁰/µ₁)⌉₊` with one absolute constant `C > 0` (uniform in `n`, `κ`,
  `M`, `q`, `β`, `δ`, the start and `µ₁`); it is `0` when `µ⁰ ≤ µ₁`. -/
theorem theorem_4_2 : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
      (κ β δ : ℝ) (x0 s0 : ι → ℝ) (mu0 mu1 : ℝ),
      IsPStarK M κ →
      1 / (8 * (1 + κ)) ≤ β → β ≤ 1 / (4 * (1 + κ)) →
      1 / (32 * Real.sqrt (Fintype.card ι) * (1 + κ)) ≤ δ →
      δ ≤ 1 / (16 * Real.sqrt (Fintype.card ι) * (1 + κ)) →
      InN2 M q β x0 s0 mu0 → 0 < mu1 →
      InN2 M q β (algorithm1 M δ x0 s0 mu0 mu1).1 (algorithm1 M δ x0 s0 mu0 mu1).2.1
          (algorithm1 M δ x0 s0 mu0 mu1).2.2.1 ∧
        (algorithm1 M δ x0 s0 mu0 mu1).2.2.1 ≤ mu1 ∧
        (algorithm1 M δ x0 s0 mu0 mu1).2.2.2 ≤
          ⌈C * (Real.sqrt (Fintype.card ι) * (1 + κ)) * Real.log (mu0 / mu1)⌉₊ := by sorry

end NewtonLCP.Supplement
