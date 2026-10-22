-- Prove2me | Theorems.Thm_GenKraus_StdForm_theorem_3
-- name    : GenKraus.StdForm.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:40.235206+00:00
-- url     : https://prove2.me/theorems/bb8b3d74-b300-4c3c-90a2-2c40c8e5e7af
-- title:
--   Theorem 3, p. 4 — the generator of a trace preserving QDS has a generalized standard form iff it is matrix normal; then 𝒟_e ⊂ 𝒟(M)
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists. Assume $\mathcal H$ is separable.
--
--   **Generalized standard form (Definition 1).** Operators $L_k$ ($k$ in a countable index set) and $M$ on $\mathcal H$, densely defined, with $M$ closed and generating a semigroup $e^{-tM}$ on $\mathcal H$, $\mathcal D(M)\subseteq\mathcal D(L_k)$ and each $L_k$ relatively bounded with respect to $M$, such that for $\varphi,\psi\in\mathcal D(M)$
--
--   $$\mathcal L(|\varphi\rangle\langle\psi|)=\sum_k|L_k\varphi\rangle\langle L_k\psi|-|M\varphi\rangle\langle\psi|-|\varphi\rangle\langle M\psi|,\qquad\sum_k\|L_k\varphi\|^2=\langle\varphi|M\varphi\rangle+\langle M\varphi|\varphi\rangle,$$
--
--   and the finite sums of such dyads form a core $\mathcal D_0$ of $\mathcal L$.
--
--   **Matrix normality (Definition 2).** There is a basis $\{e_k\}$ of $\mathcal H$ such that $\mathcal D_e^2=\operatorname{lin}\{|e_k\rangle\langle e_\ell|\}$ is a core for $\mathcal L$.
--
--   **Theorem.** $\mathcal L$ has a generalized standard form if and only if the QDS is matrix normal. In this case $\mathcal D_e\subset\mathcal D(M)$: for every basis $\{e_k\}$ witnessing matrix normality there is a generalized standard form whose $M$ satisfies
--
--   $$\operatorname{lin}\{e_k\}\subseteq\mathcal D(M).$$
--
--   The theorem says that the generators of trace preserving quantum dynamical semigroups that admit a Lindblad-type representation by (possibly unbounded) Hilbert-space operators are exactly those determined by their action on the matrix units of some basis.
--
--   **Formalization Note** The semigroup is the published `TraceDynamicalSemigroup` (linear, completely positive at every matrix level, trace non-increasing, weakly continuous) together with the two local hypotheses `IsTracePreserving` and `IsStronglyContinuous` (trace-norm continuity at $t=0$); together these are the paper's standing assumption on p. 3. The generator is the published trace-norm right-derivative graph `InTraceGeneratorGraph`, so statements quantify over graph values $\eta=\mathcal L(\rho)$ rather than a chosen value. A "basis" $\{e_k\}$ is an orthonormal set $v$ with dense linear span; $\mathcal D_e$ is its span and $\mathcal D_e^2$ the span of the dyads $|a\rangle\langle c|$, $a,c\in v$. Definition 1 is the structure `GenStdForm`, stated in the paper's equivalent form (19)–(20) (p. 11), with (3) required on dyads of $\mathcal D(M)$ and trace-norm convergence of the Kraus sums, (4) as an equality of quadratic forms on all of $\mathcal D(M)$, and the core clause for $\mathcal D_0$; "has a generalized standard form" is `Nonempty (GenStdForm T)`. The clause "$\mathcal D_e\subset\mathcal D(M)$" is stated for every basis witnessing matrix normality, which is what the construction of §3.1 (Definition 5) gives.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 4, Theorem 3

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Theorem 3, p. 4: the generator ℒ of a trace preserving QDS has a generalized standard form
if and only if the QDS is matrix normal; in this case 𝒟_e ⊂ 𝒟(M). -/
theorem theorem_3 [TopologicalSpace.SeparableSpace H] (T : TraceDynamicalSemigroup b)
    (htp : IsTracePreserving T) (hsc : IsStronglyContinuous T) :
    (Nonempty (GenStdForm T) ↔ IsMatrixNormal T) ∧
      ∀ v : Set H, IsMatrixNormalWith T v →
        ∃ S : GenStdForm T, (Submodule.span ℂ v : Set H) ⊆ (S.M.domain : Set H) := by sorry

end GenKraus.StdForm
