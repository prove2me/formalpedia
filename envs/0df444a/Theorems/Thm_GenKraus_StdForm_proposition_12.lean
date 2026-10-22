-- Prove2me | Theorems.Thm_GenKraus_StdForm_proposition_12
-- name    : GenKraus.StdForm.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:28.772+00:00
-- url     : https://prove2.me/theorems/db3bba61-9362-4b5b-ac0d-054332ae7c1f
-- title:
--   Proposition 12, p. 10 — a generalized standard form yields a basis with 𝒟_e a core for M and 𝒟²_e a core for ℒ
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists. Assume $\mathcal H$ is separable.
--
--   If $\mathcal L$ has a generalized standard form $(M,(L_k))$, there is a basis $\{e_k\}$ of $\mathcal H$ such that
--
--   1. $\mathcal D_e=\operatorname{lin}\{e_k\}\subseteq\mathcal D(M)$ is a core for $M$: every $(x,Mx)$, $x\in\mathcal D(M)$, is a limit of $(y,My)$ with $y\in\mathcal D_e$;
--   2. $\mathcal D_e^2$ is a core for $\mathcal L$ (so the QDS is matrix normal).
--
--   This is the "standard form $\Rightarrow$ matrix normal" half of Theorem 3.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. A generalized standard form is the structure `GenStdForm` (Definition 1 in the paper's equivalent form (19)–(20)); $\mathcal M(|\varphi\rangle\langle\psi|)=|M\varphi\rangle\langle\psi|+|\varphi\rangle\langle M\psi|$ is `GenStdForm.calM`, and $\mathcal L_+=\mathcal L+\mathcal M$ on a dyad is written as the graph value $\eta$ plus this sum. Trace norms are applied only to trace-class operators (a graph value plus finitely many dyads), where the published `traceNormValue` is the nuclear norm.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 10, Proposition 12

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Proposition 12, p. 10: for a generator in generalized standard form there is a basis {e_k}
such that 𝒟_e is a core for M and 𝒟²_e is a core for ℒ. -/
theorem proposition_12 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) (S : GenStdForm T) :
    ∃ v : Set H, IsMatrixNormalWith T v ∧ (Submodule.span ℂ v : Set H) ⊆ S.M.domain ∧
      ∀ x : S.M.domain, ∀ ε > 0, ∃ y : S.M.domain, (y : H) ∈ Submodule.span ℂ v ∧
        ‖(x : H) - y‖ < ε ∧ ‖S.M x - S.M y‖ < ε := by sorry

end GenKraus.StdForm
