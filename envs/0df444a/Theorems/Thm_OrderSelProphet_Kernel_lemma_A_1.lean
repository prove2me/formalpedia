-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_A_1
-- name    : OrderSelProphet.Kernel.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:56:32.214409+00:00
-- url     : https://prove2.me/theorems/3f709d68-1e55-4aaa-92a3-8769dfa9ec43
-- title:
--   Lemma A.1 — threshold paths $y=A^{\leftarrow}\circ B$: continuity, endpoints, change of variables (71) and $dB=P(U\le y)\,dy$ (72)
-- statement:
--   Let $U$ be a random variable with values in $[0,1]$ (law $\nu$), $A(x)=\mathbb E[(x-U)_+]$ for $x\in[0,1]$ and $\mu=A(1)$. Let $B$ be continuous and nondecreasing on $[0,1]$ with $B(0)=0$, $B(1)=\mu$, and $y=A^{\leftarrow}\circ B$. Then:
--
--   (a) $y$ is continuous and nondecreasing on $[0,1]$, $y(0)=\max\{x\in[0,1]:A(x)=0\}$, $y(1)=1$, and $A(y(t))=B(t)$ for all $t\in[0,1]$;
--
--   (b) $U\ge y(0)$ almost surely;
--
--   (c) for every Borel $g\ge0$ and $0\le s\le t\le1$, $\int_{(s,t]}g(y(\tau))\,dy(\tau)=\int_{y(s)}^{y(t)}g(x)\,dx$;
--
--   (d) as measures on $(0,1]$, $dB(\tau)=P(U\le y(\tau))\,dy(\tau)$.
--
--   Differences from the source:
--   - encoding: a random variable U with values in [0,1] → its law ν, a probability measure on ℝ with ν([0,1]ᶜ) = 0; A(x) = ∫ (x − u)_+ dν(u); reason: the lemma depends on U only through its law; the printed second expression ∫_0^x P(U<z)dz of A is an identity, not a hypothesis
--   - encoding: B : [0,1] → [0, μ] continuous and nondecreasing → B : ℝ → ℝ, continuous and nondecreasing on [0,1] with B(0) = 0 and B(1) = μ; reason: the range [0, μ] follows from monotonicity and the endpoint values
--   - encoding: y(0) = max{x ∈ [0,1] : A(x) = 0} → IsGreatest {x ∈ [0,1] | A x = 0} (y 0); reason: same statement: the maximum exists and equals y(0)
--   - encoding: Lebesgue–Stieltjes integrals against B and y on (0,1], no mass at t = 0 → lsMeasure f: the Stieltjes measure of the right-continuous version of f extended constantly outside [0,1], integrated over Ioc 0 1; reason: for the continuous nondecreasing B and y used here this is the Lebesgue–Stieltjes measure df on (0,1]
--   - encoding: Borel g ≥ 0 and ∫_{y(s)}^{y(t)} g dx → measurable g : ℝ → [0,∞] and the lower Lebesgue integral over (y(s), y(t)]; reason: nonnegative Borel functions; endpoints have Lebesgue measure zero
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma A.1, p. 36

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma A.1 (Threshold paths), p. 36. `ν` is the law of a random variable `U` with values in
`[0,1]`, `A(x) = E[(x - U)_+]`, `μ = A(1)`, `B` continuous and nondecreasing on `[0,1]` with
`B(0) = 0`, `B(1) = μ`, and `y = A^← ∘ B`. -/
theorem lemma_A_1 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0)
    (B : ℝ → ℝ) (hBc : ContinuousOn B (Icc 0 1)) (hBm : MonotoneOn B (Icc 0 1))
    (hB0 : B 0 = 0) (hB1 : B 1 = ∫ u, max (1 - u) 0 ∂ν) :
    let A : ℝ → ℝ := fun x => ∫ u, max (x - u) 0 ∂ν
    let y : ℝ → ℝ := threshold A B
    (ContinuousOn y (Icc 0 1) ∧ MonotoneOn y (Icc 0 1) ∧
        IsGreatest {x ∈ Icc (0 : ℝ) 1 | A x = 0} (y 0) ∧ y 1 = 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, A (y t) = B t) ∧
      ν (Iio (y 0)) = 0 ∧
      (∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
        ∫⁻ τ in Ioc s t, g (y τ) ∂(lsMeasure y) = ∫⁻ x in Ioc (y s) (y t), g x) ∧
      (lsMeasure B).restrict (Ioc 0 1) =
        ((lsMeasure y).restrict (Ioc 0 1)).withDensity (fun τ => ν (Iic (y τ))) := by sorry

end OrderSelProphet.Kernel
