-- Prove2me | Theorems.Thm_OAI_MainGap_signal_coefficient
-- name    : OAI.MainGap.signal_coefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:56:35.231253+00:00
-- url     : https://prove2.me/theorems/1a79ce4b-9922-4d10-b0b5-3e17cd08bf2e
-- title:
--   Under Property P a norm-signalling element $p$ of the ramp subalgebra of $a$ yields $w$ with $(pw)^*a(pw)\approx a$ and $\|pw\|\le\delta^{-1/2}$
-- statement:
--   Let $A$ be a C*-algebra, possibly non-unital, with its usual order: $x\le y$ means that $y-x$ is positive (self-adjoint with spectrum in $[0,\infty)$). Let $\widetilde A$ be the unitization of $A$, which contains $A$ as an ideal. The statement uses the following notions.
--
--   - For $h\in A$, $\operatorname{Her}(h)$ is the norm closure of $\{hxh^*:\ x\in A\}$; for positive $h$ it is the hereditary C*-subalgebra $\overline{hAh}$.
--   - For positive $a$ and real $l\ge0$, $(a-l)_+$ is obtained from $a$ by continuous functional calculus with $t\mapsto\max(t-l,0)$. For $\delta>0$ the *ramp* of $a$ is $g_\delta(a)$, where
--   $$g_\delta(t)=\min\Bigl(1,\ \frac{\max(t-\delta,0)}{\delta}\Bigr);$$
--   thus $g_\delta$ vanishes on $(-\infty,\delta]$, increases linearly on $[\delta,2\delta]$ and equals $1$ on $[2\delta,\infty)$.
--   - An element $p\in A$ is a *norm signal* for $x\in A$ if for every complex Hilbert space $H$ and every unital $*$-homomorphism $R:\widetilde A\to B(H)$ one has: $\|R(x)\|>\tfrac12$ implies $\|R(p)\|=1$.
--   - $A$ has *Property P* if every positive $h\in A$ is properly infinite in the following matricial sense: there are $x_j,y_j\in A$ $(j\in\mathbb{N})$ such that, as $j\to\infty$,
--   $$\begin{pmatrix}x_j^*hx_j&x_j^*hy_j\\ y_j^*hx_j&y_j^*hy_j\end{pmatrix}\longrightarrow\begin{pmatrix}h&0\\0&h\end{pmatrix}\quad\text{in }M_2(A),$$
--   that is, $r_j^*\,h\,r_j\to\operatorname{diag}(h,h)$ for the rows $r_j=(x_j\ \ y_j)\in M_{1,2}(A)$.
--
--   **Theorem.** Suppose $A$ has Property P. Let $a\in A$ be positive with $\|a\|\le1$, and let $\delta,\rho$ be real numbers with $0<\delta<\tfrac12$ and $0<\rho\le2\delta$. Let $p\in\operatorname{Her}\bigl(g_\delta(a)\bigr)$ be a norm signal for $g_\delta(a)$. Then there is $w\in A$ such that
--   $$\bigl\|(pw)^*\,a\,(pw)-a\bigr\|<2\delta+\rho\qquad\text{and}\qquad\|pw\|\le\sqrt{\delta^{-1}} .$$
--
--   So the element $s=pw$ almost reproduces $a$ under the conjugation $y\mapsto s^*ys$, with an error controlled by $\delta$ and $\rho$, while its norm is bounded by $\delta^{-1/2}$ independently of $\rho$. Since $s$ is a right multiple of $p$, estimates that hold on the hereditary subalgebra $\operatorname{Her}(p)$, such as smallness of off-diagonal compressions $\|x\,c\,k\|$, transfer to $s$. This is the coefficient step of the diagonalization argument, in which elements $p,q$ produced by an iterated separation procedure are turned into $s=pw$ and $t=qz$.
--
--   **Formalization Note** Property P is `PropertyP A` from the comparison module: `∀ h, 0 ≤ h → ProperlyInfinite h`, where `ProperlyInfinite h` is `FiniteCuntzLE (doubleCorner h) (scalarCorner h)`, i.e. there is `r : ℕ → CStarMatrix (Fin 1) (Fin 2) A` with `(r j).conjTranspose * scalarCorner h * r j` tending to `doubleCorner h` (the matrix topology is the entrywise one). The ramp is `ramp a δ (2*δ) = cfcₙ (rampFn δ (2*δ)) a` with `rampFn l u t = min 1 (max (t-l) 0 / (u-l))`, and $\operatorname{Her}$ is `Her`. `NormSignal x p` quantifies over all `HilbertRep (Unitization ℂ A)` whose Hilbert space lies in the same universe as $A$; such a representation is a unital star-algebra homomorphism `Unitization ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)`. The norm bound is written `Real.sqrt δ⁻¹`. The order is the spectral order, installed by local instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean#L109-L144

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.signalCoefficientPartialOrder
attribute [local instance] OAI.MainGap.signalCoefficientStarOrderedRing
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.signal_coefficient (hP : PropertyP A) {a p : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1/2) (hρ : 0 < ρ) (hρδ : ρ ≤ 2*δ)
    (hpH : p ∈ Her (ramp a δ (2*δ))) (hsignal : NormSignal (ramp a δ (2*δ)) p) :
    ∃ w : A, ‖star (p*w)*a*(p*w)-a‖ < 2*δ+ρ ∧
      ‖p*w‖ ≤ Real.sqrt δ⁻¹ := by sorry
