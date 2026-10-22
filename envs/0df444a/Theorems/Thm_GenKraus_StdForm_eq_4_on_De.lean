-- Prove2me | Theorems.Thm_GenKraus_StdForm_eq_4_on_De
-- name    : GenKraus.StdForm.eq_4_on_De
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:13.854429+00:00
-- url     : https://prove2.me/theorems/c56626ac-f3fc-46fb-ad17-6dee39b65be3
-- title:
--   pp. 6–7, Proof of Equation (4) — Σ_k ‖L_kφ‖² = ⟨φ|Mφ⟩ + ⟨Mφ|φ⟩ on the skeleton domain 𝒟_e
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   Assume the QDS is matrix normal with respect to a basis $\{e_k\}$, fix a unit vector $\chi\in\mathcal D_e$, and let $M$ and $\mathcal L_+$ be as in Definition 5 and Proposition 6. Suppose $(L_k)_{k}$ is a countable family of linear maps $L_k:\mathcal D_e\to\mathcal H$ representing the expander on $\mathcal D_e$ (the "algebraic skeleton", p. 6): for some orthonormal basis $\{f_j\}$ of $\mathcal H$, all $\varphi,\psi\in\mathcal D_e$ and all $g,h\in\operatorname{lin}\{f_j\}$,
--
--   $$\langle g|\mathcal L_+(|\varphi\rangle\langle\psi|)|h\rangle=\sum_k\langle g|L_k\varphi\rangle\langle L_k\psi|h\rangle .$$
--
--   Then Equation (4) holds on the form domain $\mathcal D_e$: for every $\varphi\in\mathcal D_e$,
--
--   $$\sum_k\|L_k\varphi\|^2=\langle\varphi|M\varphi\rangle+\langle M\varphi|\varphi\rangle .$$
--
--   From this identity the paper derives the relative boundedness of the $L_k$ with respect to $M$ and extends them to $\mathcal D(M)$.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. $M$ is the operator of Definition 5 for a unit vector $\chi\in\mathcal D_e$: $\mathcal D(M)=\{\psi: |\psi\rangle\langle\chi|\in\mathcal D(\mathcal L)\}$ and $M\psi=-\mathcal L(|\psi\rangle\langle\chi|)\chi+\tfrac12\langle\chi|\mathcal L(|\chi\rangle\langle\chi|)|\chi\rangle\psi$ (`contractorDomain`, `contractor`), stated as a set and a function because linearity of the domain is part of what is to be shown. $\mathcal L_+(|\varphi\rangle\langle\psi|)=\mathcal L(|\varphi\rangle\langle\psi|)+|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `expander`. The representation hypothesis is what Theorem 14 and Corollary 16 provide (matrix elements on $\mathcal D_f$, with $L_k\varphi\in\mathcal H$); it is stated for an arbitrary orthonormal basis $\{f_j\}$. The series converges unconditionally, as a sum of nonnegative reals.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, pp. 6–7, Proof of Equation (4) (after Proposition 6)

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- pp. 6–7, Proof of Equation (4): if ℒ₊(|φ⟩⟨ψ|) = Σ_k L_k|φ⟩⟨ψ|L_k† on 𝒟_e, as forms on 𝒟_f
for an orthonormal basis f, with generalized Kraus operators L_k : 𝒟_e → ℋ, then
Σ_k ‖L_kφ‖² = ⟨φ|Mφ⟩ + ⟨Mφ|φ⟩ for every φ ∈ 𝒟_e (M of Definition 5). -/
theorem eq_4_on_De [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (v : Set H)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) (hmn : IsMatrixNormalWith T v)
    (χ : H) (hχ : χ ∈ Submodule.span ℂ v) (hχ1 : ‖χ‖ = 1)
    {J : Type*} (f : HilbertBasis J ℂ H)
    {κ : Type} [Countable κ] (L : κ → Submodule.span ℂ v →ₗ[ℂ] H)
    (hL : ∀ (φ ψ : Submodule.span ℂ v) (g h : Submodule.span ℂ (Set.range f)),
      HasSum (fun k => inner ℂ (g : H) (L k φ) * inner ℂ (L k ψ) (h : H))
        (inner ℂ (g : H) (expander T χ φ ψ h))) :
    ∀ φ : Submodule.span ℂ v, HasSum (fun k => ((‖L k φ‖ ^ 2 : ℝ) : ℂ))
      (inner ℂ (φ : H) (contractor T χ φ) + inner ℂ (contractor T χ φ) (φ : H)) := by sorry

end GenKraus.StdForm
