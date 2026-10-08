-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_theorem_2_5
-- name    : NagaevLD.GenMoment.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:47.303582+00:00
-- url     : https://prove2.me/theorems/4ca0307f-2ab2-4f68-a6b5-0243546b2672
-- title:
--   Theorem 2.5, (2.44), p. 767 — P(S_n ≥ x) ≤ Π(b_j(x/n) + b_gj)exp{−ng(x/n)} for g with positive nondecreasing g′
-- statement:
--   Let $n\ge1$ and let $X_1,\dots,X_n$ be independent real random variables with distribution functions $F_j(u)=P(X_j<u)$, and $S_n=X_1+\dots+X_n$. Let $g:\mathbb R\to\mathbb R$ have a positive nondecreasing derivative $g'$, and put
--   $$b_{gj}=\int_{u\ge 0}e^{g(u)}\,dF_j(u),\qquad b_j(s)=e^{g(0)}\int_{u<0}e^{g'(s)u}\,dF_j(u).$$
--   Assume each $b_{gj}$ is finite. Then for any $x>0$,
--   $$P(S_n\ge x)\ \le\ \prod_{j=1}^n\big(b_j(x/n)+b_{gj}\big)\exp\{-ng(x/n)\}.$$
--
--   This bound, obtained by S. K. Sakoyan and Nagaev, controls the upper tail of a sum of independent summands through the generalized moments $b_{gj}$, which can be much smaller than power moments when the right tails decay like $e^{-g}$. For fixed $n$ and $x\to\infty$, $\prod_j(b_j(x/n)+b_{gj})\to\prod_j b_{gj}$, so the bound has the exponential order $e^{-ng(x/n)}$.
--
--   **Formalization Note** The summands are measurable and mutually independent (`iIndepFun`), indexed by `Fin n`. The finiteness of each $b_{gj}$ is an explicit integrability hypothesis: the page treats $b_{gj}$ as a finite factor, and Lean's integral of a non-integrable function is $0$, which would make the bound false rather than trivial. The paper defines $b_{gi}$ over $u>0$ (p. 759); the formalization integrates over $u\ge 0$, the reading the proof uses, because with $u>0$ the inequality fails (see the definition file). The hypotheses on $g$ — differentiability, $g'>0$, $g'$ nondecreasing — are imposed on $[0,\infty)$ only, the region where $g$ and $g'$ are evaluated; they imply that $g$ is nondecreasing with $g(u)\to\infty$, the standing assumption of §2. The paper's implicit $n\ge1$ is explicit in Lean, avoiding $x/0$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 767, Theorem 2.5, (2.44); b_gi from p. 759

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Theorem 2.5, (2.44), p. 767 (Nagaev–Sakoyan): if `g` has a positive nondecreasing
derivative `g′`, then for any `x > 0`,
`P(S_n ≥ x) ≤ ∏_{j=1}^n (b_j(x/n) + b_gj) · exp{−n g(x/n)}`. -/
theorem theorem_2_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (hbg : ∀ j, IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω}
      ≤ (∏ j, (bj P X g g' j (x / n) + bg P X g j)) * Real.exp (-(n * g (x / n))) := by sorry

end NagaevLD.GenMoment
