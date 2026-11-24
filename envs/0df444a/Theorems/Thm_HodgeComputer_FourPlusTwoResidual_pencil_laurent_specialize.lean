-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_pencil_laurent_specialize
-- name    : HodgeComputer.FourPlusTwoResidual.pencil_laurent_specialize
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:39.161494+00:00
-- url     : https://prove2.me/theorems/5e46aed4-23ee-4767-8aa4-6c5d0ca7bf47
-- title:
--   Specialization of a finite polar Laurent current chain along a linear pencil P + eps S
-- statement:
--   Let $D_P(q) = \frac{2}{3} q(P) - P \operatorname{div}(q)$ (`chartCurrent`). Suppose a rational current for a pencil $P + \varepsilon S$ ($P \neq 0$) has a pole of order at most $m$ at $\varepsilon = 0$, yielding Laurent coefficients $q_0, \dots, q_{m+1}$ with $q_{m+1} = 0$, $D_P(q_0) + D_S(q_1) = A$, and $D_P(q_{j+1}) + D_S(q_{j+2}) = 0$ for all $0 \le j < m$. Then the binomial specialization
--
--   $$
--   Q = \sum_{j=0}^m \binom{-2/3}{j} \left(\frac{S}{P}\right)^j q_j
--   $$
--
--   satisfies $D_P(Q) = A$ at $\varepsilon = 0$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

theorem HodgeComputer.FourPlusTwoResidual.pencil_laurent_specialize :
    ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K]
      (δ : ι → Derivation ℚ K K) (P S A : K),
      P ≠ 0 →
      ∀ (q : ℕ → ι → K) (m : ℕ),
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (q 0) +
            HodgeComputer.FourPlusTwoResidual.chartCurrent δ S (q 1) = A →
        (∀ j, j < m →
          HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (q (j + 1)) +
              HodgeComputer.FourPlusTwoResidual.chartCurrent δ S (q (j + 2)) = 0) →
        q (m + 1) = 0 →
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P
            (HodgeComputer.FourPlusTwoResidual.laurentCorrected (S / P) q m) = A := by sorry
