-- Prove2me | Theorems.Thm_GenKraus_StdForm_lemma_10
-- name    : GenKraus.StdForm.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:06.37398+00:00
-- url     : https://prove2.me/theorems/d35df646-7e79-4f96-9aea-85dfc2fa7e46
-- title:
--   Lemma 10, p. 9 — ‖ℒ₊(|φ⟩⟨ψ|)‖₁ ≤ (‖ℒ₊(|φ⟩⟨φ|)‖₁)^{1/2} · (‖ℒ₊(|ψ⟩⟨ψ|)‖₁)^{1/2} on 𝒟(M)
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume $\mathcal L$ has a generalized standard form $(M,(L_k))$ and let $\mathcal L_+=\mathcal L+\mathcal M$ with $\mathcal M(|\varphi\rangle\langle\psi|)=|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$. For all $\varphi,\psi\in\mathcal D(M)$,
--
--   $$\|\mathcal L_+(|\varphi\rangle\langle\psi|)\|_1\le\big(\|\mathcal L_+(|\varphi\rangle\langle\varphi|)\|_1\big)^{1/2}\cdot\big(\|\mathcal L_+(|\psi\rangle\langle\psi|)\|_1\big)^{1/2}.$$
--
--   This Cauchy–Schwarz type bound lets the approximation of Lemma 11 handle non-positive dyads.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A generalized standard form is the structure `GenStdForm` (Definition 1 in the paper's equivalent form (19)–(20)); $\mathcal M(|\varphi\rangle\langle\psi|)=|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `GenStdForm.calM`, and $\mathcal L_+=\mathcal L+\mathcal M$ on a dyad is written as the graph value $\eta$ plus this sum. Trace norms are applied only to trace-class operators (a graph value plus finitely many dyads), where the published `traceNormValue` is the nuclear norm. The exponent $1/2$ is the real square root `Real.sqrt`.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 9, Lemma 10

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Lemma 10, p. 9: for φ, ψ ∈ 𝒟(M),
‖ℒ₊(|φ⟩⟨ψ|)‖₁ ≤ (‖ℒ₊(|φ⟩⟨φ|)‖₁)^{1/2} · (‖ℒ₊(|ψ⟩⟨ψ|)‖₁)^{1/2}, where ℒ₊ = ℒ + 𝓜. -/
theorem lemma_10 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (htp : IsTracePreserving T)
    (hsc : IsStronglyContinuous T) (S : GenStdForm T) (φ ψ : S.M.domain)
    (ρ η ρ₁ η₁ ρ₂ η₂ : TraceClass H)
    (hρ : ρ.val = dyad (φ : H) ψ) (hη : InTraceGeneratorGraph T ρ η)
    (hρ₁ : ρ₁.val = dyad (φ : H) φ) (hη₁ : InTraceGeneratorGraph T ρ₁ η₁)
    (hρ₂ : ρ₂.val = dyad (ψ : H) ψ) (hη₂ : InTraceGeneratorGraph T ρ₂ η₂) :
    traceNormValue (η.val + S.calM φ ψ) ≤
      Real.sqrt (traceNormValue (η₁.val + S.calM φ φ)) *
        Real.sqrt (traceNormValue (η₂.val + S.calM ψ ψ)) := by sorry

end GenKraus.StdForm
