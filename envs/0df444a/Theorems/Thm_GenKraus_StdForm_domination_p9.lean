-- Prove2me | Theorems.Thm_GenKraus_StdForm_domination_p9
-- name    : GenKraus.StdForm.domination_p9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:22.760707+00:00
-- url     : https://prove2.me/theorems/a2344dff-3280-486d-b392-58f2d90cd751
-- title:
--   p. 9, after Definition 9 — 0 ≤ Tr ℒ₊(ρ) = Tr 𝓜(ρ) ≤ ‖𝓜(ρ)‖₁ for positive ρ ∈ 𝒟₀ (the expander is dominated by 𝓜)
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume $\mathcal L$ has a generalized standard form $(M,(L_k))$ and let $\mathcal M(\rho)=M\rho+\rho M^\dagger$ (15) on $\mathcal D_0$ and $\mathcal L_+=\mathcal L+\mathcal M$. For every positive $\rho\in\mathcal D_0$, written $\rho=\sum_{n=1}^N|\varphi_n\rangle\langle\varphi_n|$ with $\varphi_n\in\mathcal D(M)$,
--
--   $$0\le\operatorname{Tr}\{\mathcal L_+(\rho)\}=\operatorname{Tr}\{\mathcal M(\rho)\}\le\|\mathcal M(\rho)\|_1,\qquad \mathcal M(\rho)=\sum_n\big(|M\varphi_n\rangle\langle\varphi_n|+|\varphi_n\rangle\langle M\varphi_n|\big).$$
--
--   This domination, together with Lemma 10, is what controls $\mathcal L_+$ in the approximation argument of Lemma 11 and Proposition 12.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A generalized standard form is the structure `GenStdForm` (Definition 1 in the paper's equivalent form (19)–(20)); $\mathcal M(|\varphi\rangle\langle\psi|)=|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `GenStdForm.calM`, and $\mathcal L_+=\mathcal L+\mathcal M$ on a dyad is written as the graph value $\eta$ plus this sum. Trace norms are applied only to trace-class operators (a graph value plus finitely many dyads), where the published `traceNormValue` is the nuclear norm. Positive elements of $\mathcal D_0$ are exactly the finite sums $\sum_n|\varphi_n\rangle\langle\varphi_n|$ with $\varphi_n\in\mathcal D(M)$ (spectral decomposition inside the finite-dimensional range), which avoids composing with the unbounded $M$. The middle term $\operatorname{Tr}\{|\mathcal M(\rho)|\}$ of the paper's display is $\|\mathcal M(\rho)\|_1$ by definition; "$0\le$" is stated as real and nonnegative.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 9, paragraph after Definition 9 (with Eq. (17))

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- p. 9, after Definition 9: the expander ℒ₊ = ℒ + 𝓜 is dominated by 𝓜: for positive
ρ = Σ_n |φ_n⟩⟨φ_n| ∈ 𝒟₀ (φ_n ∈ 𝒟(M)),
0 ≤ Tr ℒ₊(ρ) = Tr 𝓜(ρ) ≤ ‖𝓜(ρ)‖₁. -/
theorem domination_p9 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (htp : IsTracePreserving T)
    (hsc : IsStronglyContinuous T) (S : GenStdForm T) (n : ℕ) (φ : Fin n → S.M.domain)
    (ρ η : TraceClass H) (hρ : ρ.val = ∑ i, dyad (φ i : H) (φ i))
    (hη : InTraceGeneratorGraph T ρ η) :
    0 ≤ (operatorTrace b (η.val + ∑ i, S.calM (φ i) (φ i))).re ∧
      (operatorTrace b (η.val + ∑ i, S.calM (φ i) (φ i))).im = 0 ∧
      operatorTrace b (η.val + ∑ i, S.calM (φ i) (φ i)) =
        operatorTrace b (∑ i, S.calM (φ i) (φ i)) ∧
      (operatorTrace b (∑ i, S.calM (φ i) (φ i))).re ≤
        traceNormValue (∑ i, S.calM (φ i) (φ i)) := by sorry

end GenKraus.StdForm
