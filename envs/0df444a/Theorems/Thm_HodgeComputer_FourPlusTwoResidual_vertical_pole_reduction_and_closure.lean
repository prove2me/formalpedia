-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_vertical_pole_reduction_and_closure
-- name    : HodgeComputer.FourPlusTwoResidual.vertical_pole_reduction_and_closure
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T19:20:27.08826+00:00
-- url     : https://prove2.me/theorems/46a1ab81-8b27-4d81-8e44-cc50f0d207ef
-- title:
--   Iterative vertical P-pole removal on the ratio chart and Gauss-Manin current closure
-- statement:
--   On the ratio chart with $z = t^2$ and $D_P(q) = \frac{2}{3} q(P) - P \operatorname{div}(q)$ (`chartCurrent`), Laurent pencil specialization produces polar sources $S_* \in F[z, 1/P(z)]$ before the rank-three Gauss-Manin fiber reduction applies. Let $\delta_2 = \partial_t$ satisfy $\delta_2(t) = 1$ and vanish on the base field $F$:
--
--   1. **Single-step vertical $P^m$-pole identity:** For any $P, a \in F[z]$ and $m \in \mathbb{N}$ with $P(t^2) \neq 0$,
--
--   $$
--   D_{P(t^2)}\!\left(0,\; 0,\; \frac{t\,a(t^2)}{P(t^2)^m}\right) = \frac{\left(2m + \frac{4}{3}\right) t^2 P'(t^2)\,a(t^2) - P(t^2)\,a(t^2) - 2 t^2 P(t^2)\,a'(t^2)}{P(t^2)^m}.
--   $$
--
--   2. **Iterative vertical $P^m$-pole removal:** Whenever $\gcd(z P'(z), P(z)) = 1$ in $F[z]$ and $P(t^2) \neq 0$, every polar source $N(t^2) / P(t^2)^m$ decomposes as $D_{P(t^2)}(0, 0, t f_{\mathrm{vert}}) + \overline{S}(t^2)$ for a vertical rational function $f_{\mathrm{vert}}$ and a denominator-free polynomial $\overline{S} \in F[z]$.
--
--   3. **Current closure:** If $D_P(q_*) = S_*$, $S_* = D_P(q_{\mathrm{vert}}) + \overline{S}$, and $D_P(q_{\mathrm{corr}}) = \overline{S} - c t^4$ for a nonzero constant $c$, then $q = (q_* - q_{\mathrm{vert}} - q_{\mathrm{corr}}) / c$ satisfies $D_P(q) = t^4$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic

theorem HodgeComputer.FourPlusTwoResidual.vertical_pole_reduction_and_closure :
    (∀ {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
      (δ : Fin 3 → Derivation ℚ L L) (t : L),
      δ 2 t = 1 →
      (∀ c : F, δ 2 (algebraMap F L c) = 0) →
      ∀ (P a : Polynomial F) (m : ℕ),
        Polynomial.aeval (t ^ 2) P ≠ 0 →
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
          (Pi.single 2 (t * (Polynomial.aeval (t ^ 2) a / (Polynomial.aeval (t ^ 2) P) ^ m))) =
          (((2 * (m : L) + 4 / 3) * t ^ 2 * Polynomial.aeval (t ^ 2) (Polynomial.derivative P) *
              Polynomial.aeval (t ^ 2) a) -
            Polynomial.aeval (t ^ 2) P * Polynomial.aeval (t ^ 2) a -
            2 * t ^ 2 * Polynomial.aeval (t ^ 2) P *
              Polynomial.aeval (t ^ 2) (Polynomial.derivative a)) /
            (Polynomial.aeval (t ^ 2) P) ^ m) ∧
    (∀ {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
      (δ : Fin 3 → Derivation ℚ L L) (t : L),
      δ 2 t = 1 →
      (∀ c : F, δ 2 (algebraMap F L c) = 0) →
      ∀ (P : Polynomial F),
        Polynomial.aeval (t ^ 2) P ≠ 0 →
        IsCoprime (Polynomial.X * Polynomial.derivative P) P →
        ∀ (m : ℕ) (N : Polynomial F),
          ∃ (f_vert : L) (S_bar : Polynomial F),
            Polynomial.aeval (t ^ 2) N / (Polynomial.aeval (t ^ 2) P) ^ m =
              HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
                (Pi.single 2 (t * f_vert)) +
              Polynomial.aeval (t ^ 2) S_bar) ∧
    (∀ {L : Type} [Field L] [CharZero L]
      (δ : Fin 3 → Derivation ℚ L L)
      (P_el t c S_star S_bar : L)
      (q_star q_vert q_corr : Fin 3 → L),
      c ≠ 0 →
      (∀ i : Fin 3, δ i c = 0) →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_star = S_star →
      S_star = HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_vert + S_bar →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_corr = S_bar - c * t ^ 4 →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el
        (fun i => (q_star i - q_vert i - q_corr i) / c) = t ^ 4) := by
  sorry
