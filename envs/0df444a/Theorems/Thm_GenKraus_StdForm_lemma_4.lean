-- Prove2me | Theorems.Thm_GenKraus_StdForm_lemma_4
-- name    : GenKraus.StdForm.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:19.524114+00:00
-- url     : https://prove2.me/theorems/35549bb2-f8a3-45a2-a05a-2c57bcfb9631
-- title:
--   Lemma 4, p. 4 — the three positivity properties of the generator of a matrix normal trace preserving QDS
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume the QDS is matrix normal with respect to a basis $\{e_k\}$ and let $\mathcal D_e=\operatorname{lin}\{e_k\}$. Then:
--
--   1. for every $\varphi\in\mathcal D_e$, $\ \langle\varphi|\mathcal L(|\varphi\rangle\langle\varphi|)|\varphi\rangle\le0$;
--   2. for every $\varphi\in\mathcal D_e$ and every $\psi\in\mathcal H$ with $\langle\varphi|\psi\rangle=0$, $\ \langle\psi|\mathcal L(|\varphi\rangle\langle\varphi|)|\psi\rangle\ge0$;
--   3. for all finite families $\varphi_1,\dots,\varphi_N\in\mathcal D_e$ and $\psi_1,\dots,\psi_N\in\mathcal H$ with $\sum_k\langle\varphi_k|\psi_k\rangle=0$,
--
--   $$\sum_{k,\ell}\langle\psi_k|\mathcal L(|\varphi_k\rangle\langle\varphi_\ell|)|\psi_\ell\rangle\ge0 .$$
--
--   Item 3 is the inequality that makes the expander $\mathcal L_+$ of Proposition 6 completely positive.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. The dyads involved lie in $\mathcal D_e^2\subseteq\mathcal D(\mathcal L)$, and each item is stated for every graph value. A complex number is "$\le0$" or "$\ge0$" when it is real (imaginary part $0$) and of that sign.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 4, Lemma 4

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Lemma 4, p. 4: the three positivity properties of the generator of a matrix normal trace
preserving QDS, on dyads of 𝒟_e = lin v ("≤ 0"/"≥ 0": real and of that sign). -/
theorem lemma_4 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (v : Set H)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) (hmn : IsMatrixNormalWith T v) :
    (∀ φ ∈ Submodule.span ℂ v, ∀ ρ η : TraceClass H, ρ.val = dyad φ φ →
        InTraceGeneratorGraph T ρ η →
        (inner ℂ φ (η.val φ)).re ≤ 0 ∧ (inner ℂ φ (η.val φ)).im = 0) ∧
    (∀ φ ∈ Submodule.span ℂ v, ∀ ψ : H, inner ℂ φ ψ = 0 → ∀ ρ η : TraceClass H,
        ρ.val = dyad φ φ → InTraceGeneratorGraph T ρ η →
        0 ≤ (inner ℂ ψ (η.val ψ)).re ∧ (inner ℂ ψ (η.val ψ)).im = 0) ∧
    (∀ (n : ℕ) (φ ψ : Fin n → H), (∀ k, φ k ∈ Submodule.span ℂ v) →
        ∑ k, inner ℂ (φ k) (ψ k) = 0 →
        ∀ η : Fin n → Fin n → TraceClass H,
          (∀ k l, ∃ ρ : TraceClass H, ρ.val = dyad (φ k) (φ l) ∧ InTraceGeneratorGraph T ρ (η k l)) →
          0 ≤ (∑ k, ∑ l, inner ℂ (ψ k) ((η k l).val (ψ l))).re ∧
            (∑ k, ∑ l, inner ℂ (ψ k) ((η k l).val (ψ l))).im = 0) := by sorry

end GenKraus.StdForm
