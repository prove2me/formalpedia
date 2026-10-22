-- Prove2me | Theorems.Thm_GenKraus_StdForm_lemma_11
-- name    : GenKraus.StdForm.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:31.563507+00:00
-- url     : https://prove2.me/theorems/bce913bd-5668-446b-92aa-ec32824b5f5f
-- title:
--   Lemma 11, p. 9 — closeness in the graph of M bounds ‖𝓜(|φ⟩⟨ψ|) − 𝓜(|e⟩⟨f|)‖₁ and ‖ℒ₊(|φ⟩⟨ψ|) − ℒ₊(|e⟩⟨f|)‖₁
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume $\mathcal L$ has a generalized standard form $(M,(L_k))$, with $\mathcal M$ and $\mathcal L_+=\mathcal L+\mathcal M$ as in Definition 9. Let $\varphi,\psi,e,f\in\mathcal D(M)$ and $\varepsilon\in\mathbb R$ with
--
--   $$\|\varphi-e\|,\ \|M\varphi-Me\|,\ \|\psi-f\|,\ \|M\psi-Mf\|\ \in[0,\varepsilon].$$
--
--   Then
--
--   $$\|\mathcal M(|\varphi\rangle\langle\psi|)-\mathcal M(|e\rangle\langle f|)\|_1\le\varepsilon\cdot(\|\varphi\|+\|M\varphi\|+\|\psi\|+\|M\psi\|+2\varepsilon),$$
--
--   $$\|\mathcal L_+(|\varphi\rangle\langle\psi|)-\mathcal L_+(|e\rangle\langle f|)\|_1\le\varepsilon\cdot(\|\varphi\|+\|M\varphi\|+\|\psi\|+\|M\psi\|+2\varepsilon).$$
--
--   Combined, these give the continuity of $\mathcal L$ on dyads in the graph norm of $M$, used in Proposition 12.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A generalized standard form is the structure `GenStdForm` (Definition 1 in the paper's equivalent form (19)–(20)); $\mathcal M(|\varphi\rangle\langle\psi|)=|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `GenStdForm.calM`, and $\mathcal L_+=\mathcal L+\mathcal M$ on a dyad is written as the graph value $\eta$ plus this sum. Trace norms are applied only to trace-class operators (a graph value plus finitely many dyads), where the published `traceNormValue` is the nuclear norm. The four norms lie in $[0,\varepsilon]$ exactly when they are $\le\varepsilon$ (norms are nonnegative), so no separate hypothesis $\varepsilon\ge0$ is needed.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 9, Lemma 11

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Lemma 11, p. 9: if (φ, ψ), (e, f) ⊂ 𝒟(M) have ‖φ−e‖, ‖Mφ−Me‖, ‖ψ−f‖, ‖Mψ−Mf‖ ∈ [0, ε],
then both ‖𝓜(|φ⟩⟨ψ|) − 𝓜(|e⟩⟨f|)‖₁ and ‖ℒ₊(|φ⟩⟨ψ|) − ℒ₊(|e⟩⟨f|)‖₁ are at most
ε · (‖φ‖ + ‖Mφ‖ + ‖ψ‖ + ‖Mψ‖ + 2ε). -/
theorem lemma_11 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (htp : IsTracePreserving T)
    (hsc : IsStronglyContinuous T) (S : GenStdForm T) (φ ψ e f : S.M.domain) (ε : ℝ)
    (h₁ : ‖(φ : H) - e‖ ≤ ε) (h₂ : ‖S.M φ - S.M e‖ ≤ ε)
    (h₃ : ‖(ψ : H) - f‖ ≤ ε) (h₄ : ‖S.M ψ - S.M f‖ ≤ ε)
    (ρ η ρ' η' : TraceClass H)
    (hρ : ρ.val = dyad (φ : H) ψ) (hη : InTraceGeneratorGraph T ρ η)
    (hρ' : ρ'.val = dyad (e : H) f) (hη' : InTraceGeneratorGraph T ρ' η') :
    traceNormValue (S.calM φ ψ - S.calM e f) ≤
        ε * (‖(φ : H)‖ + ‖S.M φ‖ + ‖(ψ : H)‖ + ‖S.M ψ‖ + 2 * ε) ∧
      traceNormValue ((η.val + S.calM φ ψ) - (η'.val + S.calM e f)) ≤
        ε * (‖(φ : H)‖ + ‖S.M φ‖ + ‖(ψ : H)‖ + ‖S.M ψ‖ + 2 * ε) := by sorry

end GenKraus.StdForm
