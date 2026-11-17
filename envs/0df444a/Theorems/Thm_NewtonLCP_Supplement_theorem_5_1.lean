-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_5_1
-- name    : NewtonLCP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:19:52.550635+00:00
-- url     : https://prove2.me/theorems/cddea8b2-2c95-4a06-ab5e-57d3f918729f
-- title:
--   Theorem 5.1 (corrected: $O$-bound rounded up) — Algorithm 1 uses $O(n^{5/4}\sqrt{1+\kappa}\log(\mu_0/\mu_1))$ solves and stays in $N^R(\beta)$
-- statement:
--   Let $M\in P_\star(\kappa)$ and $q\in\mathbb R^n$ with $n\ge1$, and choose
--
--   $$\beta\in\Big[\frac{1}{20480\,n^{3/2}},\frac{1}{16384\,n^{3/2}}\Big],\qquad \delta\in\Big[\frac{1}{9160\,n^{5/4}\sqrt{1+\kappa}},\frac{1}{4580\,n^{5/4}\sqrt{1+\kappa}}\Big].$$
--
--   For every initial point $(x^0,s^0,\mu^0)$ in the Rump neighbourhood $N^R(\beta)$ and every target $\mu_1>0$, Algorithm 1 returns $(x_{\mathrm{out}},s_{\mathrm{out}},\mu_{\mathrm{out}})$ with
--
--   1. $(x_{\mathrm{out}},s_{\mathrm{out}},\mu_{\mathrm{out}})\in N^R(\beta)$ (in particular $(x_{\mathrm{out}},s_{\mathrm{out}})\in\mathcal F_{>0}(M,q)$ and $\mu_{\mathrm{out}}>0$);
--   2. $\mu_{\mathrm{out}}\le\mu_1$;
--   3. the number of linear system solves is at most $\big\lceil C\,n^{5/4}\sqrt{1+\kappa}\,\log(\mu^0/\mu_1)\big\rceil_+$,
--
--   where $C>0$ is an absolute constant, independent of $n$, $\kappa$, $M$, $q$, $\beta$, $\delta$, the start and $\mu_1$.
--
--   This is the first improvement of the dependence on the handicap from $1+\kappa$ to $\sqrt{1+\kappa}$, obtained by measuring centrality in the norm weighted by Rump weights.
--
--   **Formalization Note** $N^R(\beta)$ is the published `InNR` (Definition 5.5, Rump weights with $K=8$); powers of $n$ are real powers; the solve count is the counter of `algorithm1`.
--
--   Differences from the source:
--   - correction: "$O(n^{5/4}\sqrt{1+\kappa}\log(\mu_0/\mu_1))$ linear system solves" → at most $\lceil C n^{5/4}\sqrt{1+\kappa}\log(\mu^0/\mu_1)\rceil_+$ solves; reason: the literal bound is false for $\mu_1$ just below $\mu^0$: $n=1$, $M=(1)$, $q=0$, $(x^0,s^0,\mu^0)=(1,1,1)$, $\mu_1=e^{-t}$ satisfies every hypothesis and uses one solve, while $Ct<1$ for $t<1/C$.
--   - encoding: $n$ arbitrary → $n\ge1$; reason: the printed ranges divide by powers of $n$ and are undefined at $n=0$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 5.1, p.14 (proof p.17, via Lemma 5.10, pp.16–17)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_InNR
import Definitions.Def_NewtonLCP_Supplement_Algorithm1

universe u

namespace NewtonLCP.Supplement

/-- **Theorem 5.1** (Algorithm 1 in the Rump neighbourhood). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 5.1, p.14 (proof p.17,
via Lemma 5.10, pp.16–17).

Let `M ∈ P⋆(κ)`, set `β ∈ [1/(20480n^{3/2}), 1/(16384n^{3/2})]` and
`δ ∈ [1/(9160n^{5/4}√(1+κ)), 1/(4580n^{5/4}√(1+κ))]` in Algorithm 1. Given an initial point
`(x⁰, s⁰, µ⁰) ∈ N^R(β)`, Algorithm 1 finds a feasible solution `(x_out, s_out, µ_out) ∈ N^R(β)`
with `µ_out ≤ µ₁` in time dominated by `O(n^{5/4}√(1+κ) · log(µ⁰/µ₁))` linear system solves.

**Formalization Note.**
* `n = Fintype.card ι ≥ 1` (`[Nonempty ι]`): the printed ranges divide by powers of `n`; the
  powers are real powers `n^{(3/2 : ℝ)}`, `n^{(5/4 : ℝ)}`.
* "`M ∈ P⋆(κ)`" is the published `IsPStarK M κ`; `N^R(β)` is the published `InNR`
  (Definition 5.5, Rump weights with `K = 8`). The ranges are the closed printed intervals.
* "Time dominated by `k` linear system solves" is "at most `k` Newton-system solves", counted by
  the solve counter of `algorithm1` (one per iteration).
* **Correction of the `O`-bound**, as in Theorem 4.2: the literal
  "`solves ≤ C·n^{5/4}√(1+κ)·log(µ⁰/µ₁)`" fails for `µ₁` just below `µ⁰` (`n = 1`, `M = (1)`,
  `q = 0`, `(x⁰, s⁰, µ⁰) = (1, 1, 1)`, `µ₁ = e^{−t}`: one solve, `C·t < 1`). The bound is
  `solves ≤ ⌈C·n^{5/4}√(1+κ)·log(µ⁰/µ₁)⌉₊` with one absolute constant `C > 0`. -/
theorem theorem_5_1 : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
      (κ β δ : ℝ) (x0 s0 : ι → ℝ) (mu0 mu1 : ℝ),
      IsPStarK M κ →
      1 / (20480 * (Fintype.card ι : ℝ) ^ ((3 : ℝ) / 2)) ≤ β →
      β ≤ 1 / (16384 * (Fintype.card ι : ℝ) ^ ((3 : ℝ) / 2)) →
      1 / (9160 * (Fintype.card ι : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt (1 + κ)) ≤ δ →
      δ ≤ 1 / (4580 * (Fintype.card ι : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt (1 + κ)) →
      InNR M q β x0 s0 mu0 → 0 < mu1 →
      InNR M q β (algorithm1 M δ x0 s0 mu0 mu1).1 (algorithm1 M δ x0 s0 mu0 mu1).2.1
          (algorithm1 M δ x0 s0 mu0 mu1).2.2.1 ∧
        (algorithm1 M δ x0 s0 mu0 mu1).2.2.1 ≤ mu1 ∧
        (algorithm1 M δ x0 s0 mu0 mu1).2.2.2 ≤
          ⌈C * ((Fintype.card ι : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt (1 + κ)) *
            Real.log (mu0 / mu1)⌉₊ := by sorry

end NewtonLCP.Supplement
