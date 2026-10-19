-- Prove2me | Theorems.Thm_OAI_UniformSparsestCut_SourceContraction_integral_bound
-- name    : OAI.UniformSparsestCut.SourceContraction.integral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:48:15.193992+00:00
-- url     : https://prove2.me/theorems/575e7e56-9ab3-426b-9d7d-20b885fc50f7
-- title:
--   The average contraction of OpenAI's cube cell functions is at most C·√d (log d)^{5/2} (OpenAI uniform sparsest cut)
-- statement:
--   **Objects** (definitions bundle `OAIQWUS000` of this split). Fix $m \in \mathbb N$ and put $d = m + 1$. `PivotFamily.PFamily d` is OpenAI's structure of pivot direction families in dimension $d$; for such an $f$, `SourceMetric.V f` is the finite vertex set of its rounded charts at scale `SourceParameters.p d 2000` $= d^{-2000}$, `SourceCharts.u f` its chart vectors and `SourceCharts.B f` its chart maps, `RoundedCharts.coordinate` the chart coordinates of a vertex, `KernelApprox.cstar` $= 2\int_0^\infty \mathrm{profile}(t)\,dt$, and `SourceMetric.err` OpenAI's macro-cost error term. `ConcreteCells.function` is OpenAI's cube cell function attached to the chart vectors, a scale and a family of functions on the vertices; $\mu$ is the uniform probability measure on the cube $(-1, 1)^d$ in $\mathbb R^d$ (`CubePoincare.cube`). `SourceContraction.H` $= \int |\rho'(t)|\,dt$ for OpenAI's mollifier $\rho$, `SourceContraction.C` $= 2(\mathrm{cstar} + \mathrm{C₀}) + \pi(1100000000 + \mathrm{C₀}\cdot H) + 1$ with `SourceMetric.C₀` $= 9 + 2\,\mathrm{cstar}$, and `SourceContraction.weight d` $= \sqrt d\,(\log d)^2\sqrt{\log d}$.
--
--   **Statement.** Let $f$ be a pivot family in dimension $d$ with $3000 \le d$, $1 \le \log d$ and $H \le d$. Let $Z : V f \to \mathbb R^{V f}$ be any map such that
--
--   - (macro) for all vertices $v, w$, $\bigl|\,\|Z v - Z w\|^2 - \mathrm{cstar}\sqrt d\,\|B_f(v) - B_f(w)\|\,\bigr| \le \mathrm{err} + 8\,d^{-8}$, where $B_f(v)$ is the chart map of $v$'s pivot applied to $v$'s chart coordinates;
--   - (local) for vertices $v, w$ in the same chart whose coordinates differ by exactly $d^{-2000}$ in $\ell^1$, $\|Z v - Z w\|^2 \le 50000000\cdot d^{-2000}\cdot d^{-5}\,(\log d)^2$.
--
--   Let $A$ be a finite type and $F : V f \to A \to \mathbb R$ with $\sum_a |F(v, a) - F(w, a)| \le \|Z v - Z w\|^2$ for all $v, w$, and let $s_0 \in \mathrm{Fin}(d^3)$. Writing $\Phi_a$ for the cube cell function of the chart vectors, scale $d^{-2000}$, family $F$, pivot $s_0$ and label $a$,
--   $$\int \sum_{a \in A} \bigl|\Phi_a(x) - \Phi_a(y)\bigr|\,d(\mu \otimes \mu)(x, y) \;\le\; C\cdot \mathrm{weight}(d).$$
--
--   The published statement spells out each hypothesis exactly; the positivity proof inside it is the one OpenAI passes to `ConcreteCells.function`.
--
--   Lean: `OAI.UniformSparsestCut.SourceContraction.integral_bound`, OpenAI's lemma of that name (in `lean/OAI/Combinatorics/SparsestCut/ContractionAverage.lean`).
-- source:
--   OpenAI, Near-square-root logarithmic integrality gaps for uniform sparsest cut, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 117; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SparsestCut/ContractionAverage.lean (declaration OAI.UniformSparsestCut.SourceContraction.integral_bound)

import Mathlib
import Definitions.Def_OAIQWUS000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
noncomputable section
variable {m : ℕ}
local notation "d" => (m+1:ℕ)
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "μ" => (CubePoincare.cube (m:=d))
lemma integral_bound (f : PivotFamily.PFamily d) (hm : 3000 ≤ d) (hl : 1≤Real.log d) (hH : H ≤ d)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt d*
         ‖B f (NeZero.pos d) v.val.1 (RoundedCharts.coordinate (u f) (p d 2000) v)-
           B f (NeZero.pos d) w.val.1 (RoundedCharts.coordinate (u f) (p d 2000) w)‖|≤err (m:=d)+8*p d 8)
    (hlocal : ∀ v w, v.val.1=w.val.1 → (∑ i, |RoundedCharts.coordinate (u f) (p d 2000) v i-
        RoundedCharts.coordinate (u f) (p d 2000) w i|)=p d 2000 →
        ‖Z v-Z w‖^2≤50000000*p d 2000*p d 5*(Real.log d)^2)
    {A : Type u1} [Fintype A] (F : V f → A → ℝ)
    (hcon : ∀ v w, (∑ a, |F v a-F w a|)≤‖Z v-Z w‖^2)
    (s0 : Fin (d^3)) :
    (∫ z : E × E, ∑ a, |ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.1-
        ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.2| ∂(μ).prod μ)≤C*weight d := by
  sorry
end
end UniformSparsestCut.SourceContraction

end

end OAI
end
