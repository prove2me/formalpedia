-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_laplace_principle_eventual
-- name    : OAI.ContinuumTemperature.laplace_principle_eventual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:58.720995+00:00
-- url     : https://prove2.me/theorems/9994f56f-6eb3-45ce-8358-0efc77dd89e6
-- title:
--   Laplace principle for sums on the volume scale L³ (OpenAI continuum temperature)
-- statement:
--   For $d \in \mathbb R$ let `densityFilter d` be the filter on pairs $(L, n) \in \mathbb R \times \mathbb N$ along which $L \to \infty$ and $n/L^3 \to d$; precisely, the preimage of $\mathrm{atTop} \times \mathcal N(d)$ under $(L, n) \mapsto (L, n/L^3)$.
--
--   Let $w : \mathbb R \to \mathbb N \to \mathbb R$, $F : \mathbb R \to \mathbb R$, $b : \mathbb N \to \mathbb R$ and $D \in \mathbb R$ satisfy:
--   - $w(L, n) > 0$ for every $L > 0$ and every $n$, and for all sufficiently large $L$ the series $\sum_n w(L, n)$ converges;
--   - $\sum_n b(n)$ converges, with $b(n) \ge 0$ for every $n$, and $D > 0$;
--   - $F(0) = 0$, and $F$ is bounded above on $[0, \infty)$;
--   - for every $d \ge 0$, $\log w(L, n) / L^3 \to F(d)$ along `densityFilter d`;
--   - for all sufficiently large $L$: $w(L, n) \le b(n)$ for every $n$ with $n/L^3 \ge D$.
--
--   Then
--   $$\lim_{L \to \infty} \frac{1}{L^3} \log \sum_{n=0}^{\infty} w(L, n) \;=\; \sup_{d \ge 0} F(d).$$
--
--   This is a Laplace principle: on the volume scale $L^3$, the sum is dominated by its largest terms, and the exponential rate of the sum is the supremum of the rates $F(d)$ of its terms at density $d$.
--
--   Lean: `OAI.ContinuumTemperature.laplace_principle_eventual`, OpenAI's theorem of that name (in `lean/OAI/Probability/ContinuumTransition/LaplaceEventual.lean`). It is the form of OpenAI's `laplace_principle` in which the sums $\sum_n w(L, n)$ need converge only for large $L$. `densityFilter` comes from the definitions bundle `OAIQWCT000` of this split.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/LaplaceEventual.lean (declaration OAI.ContinuumTemperature.laplace_principle_eventual)

import Mathlib
import Definitions.Def_OAIQWCT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem laplace_principle_eventual {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ᶠ L in atTop, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  sorry

end ContinuumTemperature
end

end OAI
end
