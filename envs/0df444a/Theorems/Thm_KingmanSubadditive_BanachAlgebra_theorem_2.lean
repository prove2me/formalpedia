-- Prove2me | Theorems.Thm_KingmanSubadditive_BanachAlgebra_theorem_2
-- name    : KingmanSubadditive.BanachAlgebra.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:51.446513+00:00
-- url     : https://prove2.me/theorems/38fd910c-17d2-4427-985f-e35f42f5c662
-- title:
--   Theorem 2, p. 885 — under S₁, S₂ and S₃′ but not S₃, x₀ₜ/t converges a.s. to ξ ∈ [−∞, ∞) with E(ξ) = −∞
-- statement:
--   Let $x=(x_{st})_{s<t}$ be a family of real random variables, indexed by nonnegative integers $s<t$, on a probability space $(\Omega,\mathcal F,P)$. Suppose that $x$ satisfies
--
--   1. **S₁**: $x_{su}\le x_{st}+x_{tu}$ whenever $s<t<u$;
--   2. **S₂**: the joint distributions of $(x_{s+1,t+1})$ are the same as those of $(x_{st})$;
--   3. **S₃′**: $E(x_{01}^+)<\infty$;
--
--   but **not** S₃ (that is, it is not the case that every $g_t=E(x_{0t})$, $t\ge1$, is finite with $g_t\ge -At$ for a constant $A$). Then the limit
--   $$\xi=\lim_{t\to\infty}\frac{x_{0t}}{t}$$
--   exists with probability one in $-\infty\le\xi<\infty$, and
--   $$E(\xi)=-\infty .$$
--
--   Theorem 2 extends Kingman's subadditive ergodic theorem (Theorem 1, which assumes S₃ and gives a finite limit with $E(\xi)=\gamma$) to the weaker moment condition S₃′; together the two theorems cover every process satisfying S₁, S₂ and S₃′. Failure of S₃ covers both possibilities named on p. 885: $g_t$ finite with $g_t/t\to-\infty$, and $g_t=-\infty$ for some $t$.
--
--   **Formalization Note** $\xi$ is a measurable $[-\infty,\infty]$-valued random variable; the conclusion asserts that almost surely $\xi<\infty$ and $x_{0t}/t\to\xi$ in the topology of $[-\infty,\infty]$, that $E(\xi^+)<\infty$ (so that $E(\xi)$ is defined), and that the extended expectation $\int\xi^+\,dP-\int\xi^-\,dP$ equals $-\infty$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, §1.2, Theorem 2, (1.2.1), (1.2.10)

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory Filter Topology

/-- **Theorem 2, §1.2, p. 885** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "If `x` satisfies S₁, S₂ and S₃′ but not S₃,
then the limit (1.2.1) exists with probability one in `−∞ ≤ ξ < ∞`, and (1.2.10) `E(ξ) = −∞`."
Here (1.2.1) is `ξ = lim_{t→∞} x₀ₜ/t`.

**Formalization Note.** `x` is a measurable family of real random variables. "Not S₃" is the
negation of S₃ exactly as defined (each `x_0t` integrable and `E(x_0t) ≥ −At`), which covers both
possibilities (1.2.8) and (1.2.9) of p. 885. The limit `ξ` is an `EReal`-valued random variable;
the convergence of `x₀ₜ/t` (a real number, embedded in `EReal`) is in the topology of `[−∞, ∞]`,
almost surely, together with `ξ < +∞`. "`E(ξ) = −∞`" is stated as: the positive part of `ξ` has
finite integral (so `E(ξ)` is defined) and the extended expectation `eMean` is `⊥`. The term at
`t = 0` (`x 0 0 / 0`) does not affect the limit. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x)
    (hnot3 : ¬ KingmanSubadditive.Ergodic.S3 P x) :
    ∃ ξ : Ω → EReal, Measurable ξ ∧
      (∀ᵐ ω ∂P, ξ ω ≠ ⊤ ∧
        Tendsto (fun t : ℕ => ((x 0 t ω / (t : ℝ) : ℝ) : EReal)) atTop (𝓝 (ξ ω))) ∧
      ∫⁻ ω, (ξ ω).toENNReal ∂P < ⊤ ∧
      eMean P ξ = ⊥ := by sorry

end KingmanSubadditive.BanachAlgebra
