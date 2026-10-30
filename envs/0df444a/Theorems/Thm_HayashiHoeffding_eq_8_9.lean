-- Prove2me | Theorems.Thm_HayashiHoeffding_eq_8_9
-- name    : HayashiHoeffding.eq_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:14.104902+00:00
-- url     : https://prove2.me/theorems/5076efe3-980d-43f6-809a-99e4f847f7ca
-- title:
--   Eqs. (8)–(9): error bounds of the test $T_{n,t}$, $1/2\le t\le 1$
-- statement:
--   Let $\rho$, $\sigma$ be density operators on a complex Hilbert space $\mathcal H$, $n \ge 1$, $a \in \mathbb R$ and $1/2 \le t \le 1$, and put
--
--   $$T_{n,t} := \{(\sigma^{\otimes n} e^{-na})^{t} - (\rho^{\otimes n})^{t} < 0\} .$$
--
--   Then $T_{n,t}$ is a test, and with $\phi(t) = \log\operatorname{Tr}\rho^{1-t}\sigma^t$,
--
--   $$\operatorname{Tr}\sigma^{\otimes n} T_{n,t} \le e^{n(1-t)a} e^{n\phi(t)} , \tag{8}$$
--
--   $$\operatorname{Tr}\rho^{\otimes n}(I - T_{n,t}) \le e^{-nta} e^{n\phi(t)} . \tag{9}$$
--
--   Together with (6)–(7) this covers every $s \in [0,1]$ in Theorem 1.
--
--   **Formalization Note** $n = k+1$ and $\rho^{\otimes n}$ is `opTensorPow ρ k`; $\{\,\cdot < 0\}$ is `negProj`; powers are `qPow` (at $t = 1$, $\rho^0$ in $\phi(1)$ is the support projection of $\rho$). The test is stated exactly as printed: with the page's substitution it is $\{X^{1-s} - Y^{1-s} > 0\}$, not the $\{\,\cdot \ge 0\}$ of Lemma 1.
--
--   Differences from the source:
--   - encoding: $n$ copies → index $k$ with $n = k + 1$; reason: the tensor powers are indexed from one copy; same instances.
--   - encoding: $e^{n\phi(t)}$ → $(\operatorname{Tr}\rho^{1-t}\sigma^t)^n$; reason: equal when the trace is positive, both $0$ when it vanishes.
--   - encoding: the projection $\{C < 0\}$ → the support projection of the negative part $C_-$; reason: Mathlib has no Borel functional calculus; same projection.
--   - encoding: traces → their real parts; reason: the traces are real.
--   - reading: $\rho^0$ at $t = 1$ (undefined on the page for singular $\rho$) → the support projection $\Pi_\rho$; reason: the limit as $t \to 1^-$; stronger reading.
--   - reading: "the projection $T_{n,t}$ satisfies" → the conclusion also states that $T_{n,t}$ is a test; reason: an orthogonal projection satisfies $0 \le T \le I$.
--   - encoding: "Hilbert space", "density operators", $\mathcal H^{\otimes n}$ → complex Hilbert space, positive trace-class operators of trace $1$ (`IsDensityOp`), completed Hilbert tensor powers (`tensorPow`, `opTensorPow`); reason: the standard meaning of these objects; no instance changes.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, eqs. (8)–(9), p.3

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

/-- **Equations (8)–(9).** Let `ρ, σ` be density operators on a complex Hilbert space `H`,
`n = k + 1`, `a ∈ ℝ` and `1/2 ≤ t ≤ 1`. The projection
`T_{n,t} = {(σ^{⊗n} e^{−na})^t − (ρ^{⊗n})^t < 0}` is a test, and
`Tr σ^{⊗n} T_{n,t} ≤ e^{n(1−t)a} e^{nφ(t)}` (8),
`Tr ρ^{⊗n} (I − T_{n,t}) ≤ e^{−nta} e^{nφ(t)}` (9),
with `φ(t) = log Tr ρ^{1−t} σ^t`.

Hayashi, arXiv:quant-ph/0611013v2, eqs. (8)–(9), p.3.

**Formalization Note.**
1. Copies are indexed `k ↦ k + 1`: `n = k + 1`, `ρ^{⊗n} = opTensorPow ρ k`.
2. `{C < 0}` is `negProj C`; powers are `qPow` (at `t = 1`, `ρ^0` in `φ(1)` is the support
   projection `Π_ρ`).
3. `e^{nφ(t)}` is written `(Tr ρ^{1−t} σ^t)^n`: equal when the trace is positive, both `0`
   when it vanishes.
4. The test is stated exactly as printed. -/
theorem eq_8_9 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ σ : H →L[ℂ] H) (hρ : IsDensityOp ρ) (hσ : IsDensityOp σ) (k : ℕ) (a t : ℝ)
    (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    let n : ℝ := (k + 1 : ℕ)
    let T : tensorPow H k →L[ℂ] tensorPow H k :=
      negProj (qPow (((Real.exp (-(n * a)) : ℝ) : ℂ) • opTensorPow σ k) t -
        qPow (opTensorPow ρ k) t)
    IsTest T ∧
    (basisOperatorTrace (opTensorPow σ k * T)).re ≤
      Real.exp (n * (1 - t) * a) * (basisOperatorTrace (qPow ρ (1 - t) * qPow σ t)).re ^ (k + 1) ∧
    (basisOperatorTrace (opTensorPow ρ k * (1 - T))).re ≤
      Real.exp (-(n * t * a)) * (basisOperatorTrace (qPow ρ (1 - t) * qPow σ t)).re ^ (k + 1) := by sorry

end HayashiHoeffding
