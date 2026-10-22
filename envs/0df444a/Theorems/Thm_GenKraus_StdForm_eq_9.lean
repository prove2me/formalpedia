-- Prove2me | Theorems.Thm_GenKraus_StdForm_eq_9
-- name    : GenKraus.StdForm.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:10.434855+00:00
-- url     : https://prove2.me/theorems/b5d0a81d-0d9c-42e9-99df-e740f20a43b4
-- title:
--   (9), p. 5 — Tr ℒ(ρ) = 0 for every ρ in the domain of the generator of a trace preserving QDS
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   For every $\rho\in\mathcal D(\mathcal L)$,
--
--   $$\operatorname{Tr}\{\mathcal L(\rho)\}=\Big[\frac{d}{dt}\operatorname{Tr}\{\mathcal T^t(\rho)\}\Big]_{t=0}=0 .$$
--
--   The identity is used twice in the paper: in Proposition 6 (as (9)) to see that $\operatorname{Tr}\mathcal L_+(\rho)=\operatorname{Tr}\{M\rho+\rho M^\dagger\}$ on $\mathcal D_e^2$, and in §3.2 (as (17)) for the domination of the expander by $\mathcal M$.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The space $\mathcal H$ is assumed separable (`SeparableSpace`), the paper's other standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 5, Eq. (9) (and p. 9, Eq. (17))

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- (9), p. 5 (and (17), p. 9): for a trace preserving QDS, Tr ℒ(ρ) = 0 for every ρ ∈ 𝒟(ℒ). -/
theorem eq_9 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b) (htp : IsTracePreserving T)
    (hsc : IsStronglyContinuous T) (ρ η : TraceClass H) (h : InTraceGeneratorGraph T ρ η) :
    operatorTrace b η.val = 0 := by sorry

end GenKraus.StdForm
