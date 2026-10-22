-- Prove2me | Theorems.Thm_GenKraus_StdForm_proposition_6
-- name    : GenKraus.StdForm.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:11.096975+00:00
-- url     : https://prove2.me/theorems/9b136163-dbdb-48b3-aea6-4095d2808f02
-- title:
--   Proposition 6, p. 5 — the expander ℒ₊ = ℒ + Mρ + ρM† is completely positive on 𝒟²_e (the paper's criterion)
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume the QDS is matrix normal with respect to a basis $\{e_k\}$, fix $\chi\in\mathcal D_e$ with $\|\chi\|=1$, and let $M$ be the operator of Definition 5,
--
--   $$M\psi=-\mathcal L(|\psi\rangle\langle\chi|)\chi+\tfrac12\langle\chi|\mathcal L(|\chi\rangle\langle\chi|)|\chi\rangle\,\psi .$$
--
--   The expander $\mathcal L_+(\rho)=\mathcal L(\rho)+M\rho+\rho M^\dagger$ (8) is completely positive on $\mathcal D_e^2$, in the form of the paper's criterion: for every $N$, all $\varphi_1,\dots,\varphi_N\in\mathcal D_e$ and all $\psi_1,\dots,\psi_N\in\mathcal H$,
--
--   $$\sum_{k,\ell=1}^N\langle\psi_k|\mathcal L_+(|\varphi_k\rangle\langle\varphi_\ell|)|\psi_\ell\rangle\ge0 .$$
--
--   This is the input to Theorem 14, which produces the Kraus operators $L_k$ of the standard form.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. $M$ is the operator of Definition 5 for a unit vector $\chi\in\mathcal D_e$: $\mathcal D(M)=\{\psi: |\psi\rangle\langle\chi|\in\mathcal D(\mathcal L)\}$ and $M\psi=-\mathcal L(|\psi\rangle\langle\chi|)\chi+\tfrac12\langle\chi|\mathcal L(|\chi\rangle\langle\chi|)|\chi\rangle\psi$ (`contractorDomain`, `contractor`), stated as a set and a function because linearity of the domain is part of what is to be shown. $\mathcal L_+(|\varphi\rangle\langle\psi|)=\mathcal L(|\varphi\rangle\langle\psi|)+|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `expander`. "$\ge0$" means real and nonnegative.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 5, Proposition 6 and the criterion for complete positivity after Eq. (10)

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Proposition 6, p. 5, in the paper's criterion for complete positivity: for a matrix normal
QDS and M of Definition 5 (unit χ ∈ 𝒟_e), Σ_{k,ℓ} ⟨ψ_k|ℒ₊(|φ_k⟩⟨φ_ℓ|)|ψ_ℓ⟩ ≥ 0 for all N,
φ_1, …, φ_N ∈ 𝒟_e and ψ_1, …, ψ_N ∈ ℋ. -/
theorem proposition_6 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (v : Set H)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) (hmn : IsMatrixNormalWith T v)
    (χ : H) (hχ : χ ∈ Submodule.span ℂ v) (hχ1 : ‖χ‖ = 1)
    (n : ℕ) (φ ψ : Fin n → H) (hφ : ∀ k, φ k ∈ Submodule.span ℂ v) :
    0 ≤ (∑ k, ∑ l, inner ℂ (ψ k) (expander T χ (φ k) (φ l) (ψ l))).re ∧
      (∑ k, ∑ l, inner ℂ (ψ k) (expander T χ (φ k) (φ l) (ψ l))).im = 0 := by sorry

end GenKraus.StdForm
