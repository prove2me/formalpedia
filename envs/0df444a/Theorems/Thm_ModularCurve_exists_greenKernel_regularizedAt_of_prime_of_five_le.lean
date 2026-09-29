-- Prove2me | Theorems.Thm_ModularCurve_exists_greenKernel_regularizedAt_of_prime_of_five_le
-- name    : ModularCurve.exists_greenKernel_regularizedAt_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1db407cf-756f-5897-a101-5bcf08704363
-- title:
--   Bounded Green kernel for chordal proximity at prime level
-- statement:
--   Fix a natural number $N$ that is prime with $5 \le N$, a family $s \colon \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, realised inside Laurent series) which is an `IsEmbBasis`, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space $\{f : \forall v,\ v(f) \le \exp(\mathrm{embDivisor}_N(v))\}$ of the divisor $\mathrm{embDegree}(N)\cdot \overline{\infty}$, an element $t$ of that field, and a prime $p$. The assertion is that there is a real constant $C$ such that for every absolute value $\mu$ on $\overline{\mathbb Q}$ which is nonarchimedean and satisfies $\mu(p) < 1$, there exist a function $g$ on ordered pairs of places of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ (places in the project's sense: proper valuation subrings containing $\overline{\mathbb Q}$ whose valuation ring is a principal ideal ring) and a function $c$ on the field, with the following six properties, where $w.\mathrm{ord}$ denotes $-\log$ of the associated discrete valuation and $P.\mathrm{evalAt}$ the residue evaluation at $P$ with values in $\overline{\mathbb Q}$. (i) $c(f_1f_2) = c(f_1) + c(f_2)$ for nonzero $f_1, f_2$. (ii) For nonzero $f$, any finitely supported divisor $D$ with $D(w) = w.\mathrm{ord}(f)$ for all $w$, and any place $P$ with $D(P) = 0$, one has $\sum_w D(w)\, g(P,w) = -\log \mu(P.\mathrm{evalAt}(f)) + c(f)$. (iii) For distinct places $P \ne Q$, $|g(P,Q) - \mathrm{prox}_\mu(\mathrm{evalVec}_s(P), \mathrm{evalVec}_s(Q))| \le C\,(-\log\mu(p))$, where $\mathrm{evalVec}_s(P)_i = P.\mathrm{evalAt}(s_i\, s_{\mathrm{pivot}}^{-1})$ and $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log\sup_i \mu(y_i) - \log \sup_{i,j}\mu(x_iy_j - x_jy_i)$. (iv) $|c(s_i)| \le C\,(-\log\mu(p))$ for every $i$. (v) For any divisor $D$ with $D(w) = w.\mathrm{ord}(t)$, the quantity $\sum_{w \ne \overline{\infty}} D(w)\,g(\overline{\infty},w) - c(t)$ is bounded in absolute value by $C\,(-\log\mu(p))$, with $\overline{\infty} =$ `cuspInftyBar N`. (vi) For every place $P$, every $u$ with $P.\mathrm{ord}(u) = 1$ and every divisor $D$ with $D(w) = w.\mathrm{ord}(u)$, the difference of $\sum_{w \ne P} D(w)\,g(P,w) - c(u)$ and $\log\sup_{i,j}\mu\bigl(\mathrm{regVal}_s(P,u,1,1)(\mathrm{evalVec}_s(P)_i \cdot s_j - \mathrm{evalVec}_s(P)_j \cdot s_i)\bigr) - 2\log\sup_i \mu(\mathrm{evalVec}_s(P)_i)$ is bounded in absolute value by $C\,(-\log\mu(p))$, where $\mathrm{regVal}_s(P,u,1,1)(x) = P.\mathrm{evalAt}(x\, s_{\mathrm{pivot}}^{-1} u^{-1})$.
--
--   This is the nonarchimedean Green (local Néron) kernel attached to the chordal proximity of the coordinate embedding of $X_0(N)$, normalised so that all error terms are multiples of $-\log\mu(p)$, together with its regularisation at the cusp and at an arbitrary place against an arbitrary uniformiser. It supplies the local input for [`ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_greenKernel_regularizedAt_of_prime_of_five_le.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_greenKernel_regularizedAt_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (p : ℕ) (hp : p.Prime) :
    ∃ C : ℝ, ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∃ (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
            Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
        (c : modularFunctionFieldBar N → ℝ),
        (∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂) ∧
        (∀ f : modularFunctionFieldBar N, f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
          ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
            (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f) ∧
        (∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
          |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ i : Fin r, |c (s i)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord t) →
          |((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * g (cuspInftyBar N) w) - c t|
            ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ u : modularFunctionFieldBar N, P.ord u = 1 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord u) →
            |((D.erase P).sum fun w n => (n : ℝ) * g P w) - c u
                - (Real.log (⨆ q : Fin r × Fin r,
                      μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
                    - 2 * Real.log (⨆ i, μ (evalVec s P i)))|
              ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by sorry
