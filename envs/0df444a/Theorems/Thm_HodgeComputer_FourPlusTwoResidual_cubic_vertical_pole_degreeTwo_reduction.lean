-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_cubic_vertical_pole_degreeTwo_reduction
-- name    : HodgeComputer.FourPlusTwoResidual.cubic_vertical_pole_degreeTwo_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T20:39:54.687952+00:00
-- url     : https://prove2.me/theorems/b264b0cc-40db-4466-8031-650749c7bb1d
-- title:
--   Degree-two vertical pole and infinity reduction onto $(1, t^2, t^4)$ for cubic ratio-chart polynomials
-- statement:
--   Let $F$ and $L$ be characteristic-zero fields such that $L$ is an $F$-algebra equipped with $\mathbb{Q}$-derivations $\delta_0, \delta_1, \delta_2 : L \to L$, and let $t \in L$ satisfy $\delta_2(t) = 1$ and $\delta_2(c) = 0$ for every $c \in F$. Write $D_P(q) = \frac{2}{3} q(P) - P \operatorname{div}(q)$ for the ratio-chart twisted divergence operator.
--
--   Suppose $P \in F[z]$ is a cubic polynomial ($\deg_z P = 3$) such that $P(t^2) \neq 0$ in $L$ and $\gcd(z P'(z), P(z)) = 1$ in $F[z]$. Then for every pole order $m \in \mathbb{N}$ and every numerator polynomial $N \in F[z]$, there exist a vertical rational component $f_{\mathrm{vert}} \in L$ and a polynomial remainder $\overline{S}(z) = s_0 + s_1 z + s_2 z^2 \in F[z]$ of degree at most $2$ such that
--
--   $$
--   \frac{N(t^2)}{P(t^2)^m} = D_{P(t^2)}\!\left(0,\; 0,\; t\,f_{\mathrm{vert}}\right) + s_0 + s_1 t^2 + s_2 t^4.
--   $$
--
--   This strengthens the polynomial remainder clause of `vertical_pole_reduction_and_closure` by bounding the vertical remainder onto the three-dimensional fiber basis $(1, t^2, t^4)$ required as input to the rank-three Gauss–Manin connection on the ratio chart, without imposing any degree bound on the specialized Laurent numerator $N$.
--
--   **Formalization Note** In Lean, $D_{P(t^2)}$ is `HodgeComputer.FourPlusTwoResidual.chartCurrent`, the degree bound is stated as `S_bar.natDegree ≤ 2` (which covers $\overline{S} = 0$ via `(0 : Polynomial F).natDegree = 0`), and $s_j$ is `algebraMap F L (S_bar.coeff j)` for $j \in \{0, 1, 2\}$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` (ratio-chart Gauss-Manin reduction `connection/gauss-manin.md` and Laurent specialization `variation/total-trace.md`), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic

theorem HodgeComputer.FourPlusTwoResidual.cubic_vertical_pole_degreeTwo_reduction :
    ∀ {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
      (δ : Fin 3 → Derivation ℚ L L) (t : L),
      δ 2 t = 1 →
      (∀ c : F, δ 2 (algebraMap F L c) = 0) →
      ∀ (P : Polynomial F),
        P.natDegree = 3 →
        Polynomial.aeval (t ^ 2) P ≠ 0 →
        IsCoprime (Polynomial.X * Polynomial.derivative P) P →
        ∀ (m : ℕ) (N : Polynomial F),
          ∃ (f_vert : L) (S_bar : Polynomial F),
            S_bar.natDegree ≤ 2 ∧
            Polynomial.aeval (t ^ 2) N / (Polynomial.aeval (t ^ 2) P) ^ m =
              HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
                (Pi.single 2 (t * f_vert)) +
              Polynomial.aeval (t ^ 2) S_bar ∧
            Polynomial.aeval (t ^ 2) S_bar =
              algebraMap F L (S_bar.coeff 0) +
              algebraMap F L (S_bar.coeff 1) * t ^ 2 +
              algebraMap F L (S_bar.coeff 2) * t ^ 4 := by
  sorry
