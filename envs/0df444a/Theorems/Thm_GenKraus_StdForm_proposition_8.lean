-- Prove2me | Theorems.Thm_GenKraus_StdForm_proposition_8
-- name    : GenKraus.StdForm.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:05.37199+00:00
-- url     : https://prove2.me/theorems/64ed45b1-382f-4fc7-a240-79dac560e588
-- title:
--   Proposition 8, p. 8 — M is maximal accretive and generates the contraction semigroup e^{−tM} on ℋ
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume the QDS is matrix normal with respect to a basis $\{e_k\}$, fix a unit vector $\chi\in\mathcal D_e$ and let $M$ be the operator of Definition 5. Then
--
--   1. $M$ is accretive: $\operatorname{Re}\langle\varphi|M\varphi\rangle\ge0$ for all $\varphi\in\mathcal D(M)$;
--   2. $M$ generates a contraction semigroup $e^{-tM}$ on $\mathcal H$: there is a strongly continuous semigroup $(C_t)_{t\ge0}$ of contractions on $\mathcal H$ such that, for all $x,y\in\mathcal H$,
--
--   $$x\in\mathcal D(M)\ \text{and}\ -Mx=y\quad\Longleftrightarrow\quad \lim_{t\downarrow0}\frac{C_tx-x}{t}=y .$$
--
--   This is the remaining property of $M$ required by Definition 1.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. $M$ is the operator of Definition 5 for a unit vector $\chi\in\mathcal D_e$: $\mathcal D(M)=\{\psi: |\psi\rangle\langle\chi|\in\mathcal D(\mathcal L)\}$ and $M\psi=-\mathcal L(|\psi\rangle\langle\chi|)\chi+\tfrac12\langle\chi|\mathcal L(|\chi\rangle\langle\chi|)|\chi\rangle\psi$ (`contractorDomain`, `contractor`), stated as a set and a function because linearity of the domain is part of what is to be shown. $\mathcal L_+(|\varphi\rangle\langle\psi|)=\mathcal L(|\varphi\rangle\langle\psi|)+|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `expander`. The contraction semigroup is the published `ContractionSemigroup`. "Maximal accretive" is stated through generation: an accretive operator that is exactly the negative generator of a contraction semigroup is maximal accretive (Lumer–Phillips).
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 8, Proposition 8

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Proposition 8, p. 8: the operator M of Definition 5 is accretive, Re⟨φ|Mφ⟩ ≥ 0 on 𝒟(M), and
it generates a contraction semigroup e^{−tM} on ℋ: −M, on exactly 𝒟(M), is its generator. -/
theorem proposition_8 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (v : Set H)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) (hmn : IsMatrixNormalWith T v)
    (χ : H) (hχ : χ ∈ Submodule.span ℂ v) (hχ1 : ‖χ‖ = 1) :
    (∀ φ ∈ contractorDomain T χ, 0 ≤ (inner ℂ φ (contractor T χ φ)).re) ∧
      ∃ C : ContractionSemigroup H, ∀ x y : H,
        (x ∈ contractorDomain T χ ∧ -contractor T χ x = y) ↔
          Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (C.maps t.toNNReal x - x))
            (𝓝[Set.Ioi 0] 0) (𝓝 y) := by sorry

end GenKraus.StdForm
