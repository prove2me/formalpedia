-- Prove2me | Theorems.Thm_HayashiHoeffding_lemma_2
-- name    : HayashiHoeffding.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:38.254779+00:00
-- url     : https://prove2.me/theorems/6cc02976-b794-483c-8ed0-65303aa64f8e
-- title:
--   Lemma 2 (Audenaert et al.): $\operatorname{Tr}\{A-B\ge 0\}B(A^t-B^t)\ge 0$
-- statement:
--   Let $A$, $B$ be positive operators on a complex Hilbert space $\mathcal H$ and $0 \le t \le 1$, and suppose $A^{1+t}$ and $B^{1+t}$ are trace class. Then
--
--   $$\operatorname{Tr}\, \{A - B \ge 0\}\, B\, (A^t - B^t) \ge 0 ,$$
--
--   where $\{A - B \ge 0\}$ is the spectral projection of $A - B$ onto $[0,\infty)$. In particular the trace is a real number.
--
--   This inequality of Audenaert et al. is the engine of the paper: applied with $A = X^{1-s}$, $B = Y^{1-s}$ and $t = s/(1-s)$ it yields Lemma 1, from which the bounds (6)–(9) on the error probabilities of the likelihood-ratio tests follow.
--
--   **Formalization Note** $\{A-B\ge 0\}$ is `nonnegProj (A - B)`; powers are `qPow`, so $A^0$ is the support projection of $A$; the inequality is in $\mathbb C$ with its partial order (`ComplexOrder`).
--
--   Differences from the source:
--   - reading: "positive-semidefinite operators A, B" → positive bounded operators with $A^{1+t}$, $B^{1+t}$ trace class; reason: in infinite dimension the trace must exist; this is the class in which the traced product is trace class and which contains the paper's application ($A^{1+t} = X$, $B^{1+t} = Y$ trace class), while $A$, $B$ themselves need not be trace class there; in finite dimension the condition is automatic.
--   - reading: $A^0$, $B^0$ at $t = 0$ (undefined on the page for singular operators) → support projections $\Pi_A$, $\Pi_B$; reason: the limit of $A^t$ as $t \to 0^+$; the alternative $A^0 = I$ makes the case $t = 0$ void.
--   - encoding: $\{A - B \ge 0\} = \sum_{c_i \ge 0} E_i$ → $I$ minus the support projection of the negative part $(A-B)_-$; reason: Mathlib has no Borel functional calculus; it is the spectral projection of $[0,\infty)$ for every self-adjoint operator.
--   - encoding: "$\ge 0$" for a trace → $0 \le z$ in the partial order of $\mathbb C$; reason: the order asserts $z$ real and nonnegative, which is what the page means.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, Lemma 2, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
import Definitions.Def_HayashiHoeffding_nonnegProj

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace
open scoped ComplexOrder

namespace HayashiHoeffding

universe u

/-- **Lemma 2 (Audenaert et al.)** For positive operators `A, B` on a complex Hilbert space and
`0 ≤ t ≤ 1`, `Tr {A − B ≥ 0} B (A^t − B^t) ≥ 0`.

Hayashi, arXiv:quant-ph/0611013v2, Lemma 2, p.3.

**Formalization Note.**
1. `{A − B ≥ 0}` is `nonnegProj (A − B) = 1 − supportProj (A − B)⁻` (spectral projection of
   `[0, ∞)`, including the kernel of `A − B`).
2. Powers are `qPow` (`A^0` is the support projection `Π_A`).
3. In infinite dimension the trace must exist: `A` and `B` are assumed to have `A^{1+t}` and
   `B^{1+t}` trace class (Schatten class `S_{1+t}`); then `B A^t` and `B^{1+t}` are trace class.
   This is the class in which the paper applies the lemma (`A = X^{1−s}`, `B = Y^{1−s}` with
   trace-class `X, Y`); in finite dimension it is automatic.
4. The inequality is in `ℂ` with `ComplexOrder`, so it also asserts the trace is real. -/
theorem lemma_2 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAtc : IsModulusTraceClass (qPow A (1 + t)))
    (hBtc : IsModulusTraceClass (qPow B (1 + t))) :
    0 ≤ basisOperatorTrace (nonnegProj (A - B) * B * (qPow A t - qPow B t)) := by sorry

end HayashiHoeffding
