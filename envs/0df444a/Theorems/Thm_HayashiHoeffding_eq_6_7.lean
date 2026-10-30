-- Prove2me | Theorems.Thm_HayashiHoeffding_eq_6_7
-- name    : HayashiHoeffding.eq_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:09.920979+00:00
-- url     : https://prove2.me/theorems/9c2b1399-edc5-4feb-b3a8-8294cd61972f
-- title:
--   Eqs. (6)–(7): error bounds of the test $T_{n,s}$, $0\le s\le 1/2$
-- statement:
--   Let $\rho$, $\sigma$ be density operators on a complex Hilbert space $\mathcal H$, $n \ge 1$, $a \in \mathbb R$ and $0 \le s \le 1/2$. Put $X = \sigma^{\otimes n} e^{-na}$, $Y = \rho^{\otimes n}$ and
--
--   $$T_{n,s} := \{(\sigma^{\otimes n} e^{-na})^{1-s} - (\rho^{\otimes n})^{1-s} < 0\} .$$
--
--   Then $T_{n,s}$ is a test ($0 \le T_{n,s} \le I$), and with $\phi(s) = \log \operatorname{Tr}\rho^{1-s}\sigma^s$,
--
--   $$\operatorname{Tr}\sigma^{\otimes n} T_{n,s} = \operatorname{Tr} X T_{n,s} e^{na} \le \operatorname{Tr} X^s Y^{1-s} e^{na} = e^{n(1-s)a} e^{n\phi(s)} , \tag{6}$$
--
--   $$\operatorname{Tr}\rho^{\otimes n}(I - T_{n,s}) \le \operatorname{Tr} X^s Y^{1-s} = e^{-nsa} e^{n\phi(s)} . \tag{7}$$
--
--   These are the non-asymptotic bounds on the two error probabilities from which the exponents of Theorem 1 are read off for $s \in [0, 1/2]$.
--
--   **Formalization Note** $n = k+1$ and $\rho^{\otimes n}$ is `opTensorPow ρ k`; $\{\,\cdot < 0\}$ is `negProj`; powers are `qPow`. Traces are compared through their real parts. The first equality of (7), $\operatorname{Tr}\rho^{\otimes n}(I - T_{n,s}) = \operatorname{Tr}Y(I-T_{n,s})$, holds by the definition of $Y$.
--
--   Differences from the source:
--   - encoding: $n$ copies → index $k$ with $n = k + 1$; reason: the tensor powers are indexed from one copy; same instances.
--   - encoding: $e^{n\phi(s)}$ → $(\operatorname{Tr}\rho^{1-s}\sigma^s)^n$; reason: equal when the trace is positive, both $0$ when it vanishes ($\phi(s) = -\infty$).
--   - encoding: the projection $\{C < 0\}$ → the support projection of the negative part $C_-$; reason: Mathlib has no Borel functional calculus; same projection.
--   - encoding: traces of positive-trace products → their real parts; reason: the traces are real, so the comparison is unchanged.
--   - reading: $X^0$, $\sigma^0$ at $s = 0$ (undefined on the page for singular operators) → support projections; reason: the limit as $s \to 0^+$; stronger reading.
--   - reading: "the projection $T_{n,s}$ satisfies" → the conclusion also states that $T_{n,s}$ is a test; reason: an orthogonal projection satisfies $0 \le T \le I$, which is what makes (6)–(7) bounds on error probabilities.
--   - encoding: the first equality of (7), $\operatorname{Tr}\rho^{\otimes n}(I - T_{n,s}) = \operatorname{Tr}Y(I - T_{n,s})$ → not restated; reason: $Y$ is $\rho^{\otimes n}$ by definition (a `let`), so the equality is an identity and the inequality of (7) is stated with $\rho^{\otimes n}$ directly.
--   - encoding: "Hilbert space", "density operators", $\mathcal H^{\otimes n}$ → complex Hilbert space, positive trace-class operators of trace $1$ (`IsDensityOp`), completed Hilbert tensor powers (`tensorPow`, `opTensorPow`); reason: the standard meaning of these objects; no instance changes.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, eqs. (6)–(7), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
import Definitions.Def_HayashiHoeffding_tensorPow
import Definitions.Def_HayashiHoeffding_opTensorPow
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_HayashiHoeffding_IsTest
import Definitions.Def_HayashiHoeffding_negProj

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace

namespace HayashiHoeffding

universe u

/-- **Equations (6)–(7).** Let `ρ, σ` be density operators on a complex Hilbert space `H`,
`n = k + 1`, `a ∈ ℝ` and `0 ≤ s ≤ 1/2`. With `X = σ^{⊗n} e^{−na}`, `Y = ρ^{⊗n}`, the projection
`T_{n,s} = {(σ^{⊗n} e^{−na})^{1−s} − (ρ^{⊗n})^{1−s} < 0}` is a test, and
`Tr σ^{⊗n} T_{n,s} = Tr X T_{n,s} e^{na} ≤ Tr X^s Y^{1−s} e^{na} = e^{n(1−s)a} e^{nφ(s)}` (6),
`Tr ρ^{⊗n} (I − T_{n,s}) ≤ Tr X^s Y^{1−s} = e^{−nsa} e^{nφ(s)}` (7),
with `φ(s) = log Tr ρ^{1−s} σ^s`.

Hayashi, arXiv:quant-ph/0611013v2, eqs. (6)–(7), p.3.

**Formalization Note.**
1. Copies are indexed `k ↦ k + 1`: `n = k + 1`, `ρ^{⊗n} = opTensorPow ρ k`.
2. `{C < 0}` is `negProj C`; powers are `qPow` (`A^0` is the support projection).
3. `e^{nφ(s)}` is written `(Tr ρ^{1−s} σ^s)^n`: equal when the trace is positive, both `0`
   when it vanishes (`φ(s) = −∞`).
4. Traces are `basisOperatorTrace`; the real parts of the (real) traces are compared.
5. The first equality of (7), `Tr ρ^{⊗n}(I − T) = Tr Y(I − T)`, holds by the definition of `Y`
   and is not repeated. -/
theorem eq_6_7 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ σ : H →L[ℂ] H) (hρ : IsDensityOp ρ) (hσ : IsDensityOp σ) (k : ℕ) (a s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    let n : ℝ := (k + 1 : ℕ)
    let X : tensorPow H k →L[ℂ] tensorPow H k :=
      ((Real.exp (-(n * a)) : ℝ) : ℂ) • opTensorPow σ k
    let Y : tensorPow H k →L[ℂ] tensorPow H k := opTensorPow ρ k
    let T : tensorPow H k →L[ℂ] tensorPow H k := negProj (qPow X (1 - s) - qPow Y (1 - s))
    IsTest T ∧
    (basisOperatorTrace (opTensorPow σ k * T)).re =
      (basisOperatorTrace (X * T)).re * Real.exp (n * a) ∧
    (basisOperatorTrace (X * T)).re * Real.exp (n * a) ≤
      (basisOperatorTrace (qPow X s * qPow Y (1 - s))).re * Real.exp (n * a) ∧
    (basisOperatorTrace (qPow X s * qPow Y (1 - s))).re * Real.exp (n * a) =
      Real.exp (n * (1 - s) * a) * (basisOperatorTrace (qPow ρ (1 - s) * qPow σ s)).re ^ (k + 1) ∧
    (basisOperatorTrace (opTensorPow ρ k * (1 - T))).re ≤
      (basisOperatorTrace (qPow X s * qPow Y (1 - s))).re ∧
    (basisOperatorTrace (qPow X s * qPow Y (1 - s))).re =
      Real.exp (-(n * s * a)) * (basisOperatorTrace (qPow ρ (1 - s) * qPow σ s)).re ^ (k + 1) := by sorry

end HayashiHoeffding
