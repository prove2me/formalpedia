-- Prove2me | Theorems.Thm_InfHorizonVP_theorem_A_1
-- name    : InfHorizonVP.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:54.999012+00:00
-- url     : https://prove2.me/theorems/e02dc57a-a611-4949-9d7a-4ba43d41d04a
-- title:
--   Theorem A.1 — Gelfand integral of the Dini–Hadamard subdifferential mapping
-- statement:
--   Let $E$ be a separable real Banach space and $I\subseteq\mathbb R$ nonempty and closed. Let $x:I\to E$ be measurable and $L:I\times E\to\mathbb R$ such that
--
--   1. $L(\cdot,z)$ is measurable for every $z\in E$;
--   2. there are $\varepsilon>0$ and an integrable $k:I\to\mathbb R$ with $|L(t,y)-L(t,z)|\le k(t)\|y-z\|$ for all $y,z\in x(t)+\varepsilon B$ and $t\in I$;
--   3. $L$ is a normal integrand: $\mathcal L\otimes\operatorname{Borel}(E)$-measurable with $L(t,\cdot)$ lower semicontinuous for every $t\in I$;
--   4. $\partial^-_xL(t,x(t))\neq\emptyset$ for a.e. $t\in I$.
--
--   Then $\partial^-_xL(\cdot,x(\cdot))$ has a Gelfand integrable selector, and its Gelfand integral $\int_I\partial^-_xL(t,x(t))\,dt$ is weakly$^*$ compact and convex with
--   $$
--   s\Bigl(v,\int_I\partial^-_xL(t,x(t))\,dt\Bigr)=\int_I s\bigl(v,\partial^-_xL(t,x(t))\bigr)\,dt\qquad\text{for every }v\in E .
--   $$
--
--   Applied to $-L(\cdot,\cdot,\dot x_0(\cdot))$ on $\mathbb R_+$, it supplies the weak$^*$ measurable selector $f$ of $\partial^+_xL(t,x_0(t),\dot x_0(t))$ from which the adjoint arc of Theorem 4.1 is built.
--
--   Differences from the source:
--   - reading: s(v, ∫_I ∂⁻ₓL dt) = ∫_I s(v, ∂⁻ₓL(t, x(t))) dt → t ↦ s(v, ∂⁻ₓL(t, x(t))) (real part) is integrable on I and its integral equals s(v, ∫_I ∂⁻ₓL dt) in EReal; reason: the equality asserts that the right side is a genuine integral; the support function is finite a.e. (subgradients are bounded by k(t))
--   - encoding: L : I × E → ℝ 𝓛 ⊗ Borel(E)-measurable → the extension of uncurry L by 0 off I × E is measurable for the Carathéodory σ-algebra ⊗ borel E; reason: equivalent since I × E is measurable
--   - encoding: functions on I; measurable x : I → E → functions on ℝ with conditions restricted to I; x NullMeasurable for Lebesgue measure on I and the Borel σ-algebra of E; reason: values off I are never used; Lebesgue measurability
--   - encoding: weakly* compact → IsCompact of the image under StrongDual.toWeakDual; reason: the weak* topology is that of WeakDual ℝ E
--   - encoding: ∂⁻φ(x̄) defined for x̄ ∈ dom φ → dhSubdiff requires φ(x̄) finite and is empty otherwise; reason: V is finite under (H1)–(H7) (Theorem 3.1), so no instance changes
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Theorem A.1, p.23 (PDF p.24), with the hypotheses of Proposition A.1, p.22

import Mathlib
import Definitions.Def_InfHorizonVP_dhSubdiff
import Definitions.Def_InfHorizonVP_IsGelfandIntegral
import Definitions.Def_InfHorizonVP_gelfandSetIntegral
import Definitions.Def_InfHorizonVP_supportFn
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Theorem A.1 — Gelfand integral of the Dini–Hadamard subdifferential mapping of a normal
integrand.**
Frankowska, Sagara, arXiv:1801.00400v3, Theorem A.1, p.23: "Under the hypothesis of Proposition
A.1, if L is a normal integrand with ∂⁻ₓL(t, x(t)) ≠ ∅ a.e. t ∈ I, then the Dini–Hadamard
subdifferential mapping ∂⁻ₓL(·, x(·)) : I ⇝ E* has a Gelfand integrable selector and the Gelfand
integral ∫∂⁻ₓL(t, x(t))dt is weakly* compact and convex with s(v, ∫_I ∂⁻ₓL(t, x(t))dt) =
∫_I s(v, ∂⁻ₓL(t, x(t)))dt for every v ∈ E." Hypotheses of Proposition A.1 (p.22): "Let E be a
separable Banach space and I be a nonempty closed subset of R. If, for a given measurable function
x : I → E, the function L : I × E → R satisfies the following conditions: (i) L(·, x) is measurable
for every x ∈ E; (ii) There exist ε > 0 and an integrable function k : I → R such that
|L(t, x) − L(t, y)| ≤ k(t)‖x − y‖ for every x, y ∈ x(t) + εB and t ∈ I". Normal integrand (p.22):
"An 𝓛 ⊗ Borel(E, ‖·‖)-measurable function L : I × E → R ∪ {+∞} is called a normal integrand if
L(t, ·) is lower semicontinuous on E for every t ∈ I."

**Formalization Note.** Functions on `I` are functions on `ℝ` whose values off `I` are ignored;
the `𝓛 ⊗ Borel(E)` measurability of `L` on `I × E` is measurability of its extension by `0` off
`I × E` (equivalent, since `I × E` is measurable). `𝓛` is the Carathéodory σ-algebra of Lebesgue
outer measure; "measurable" for functions of `t` is `NullMeasurable` for Lebesgue measure on `I`
(for `x : I → E`, with the Borel σ-algebra of `E`).
`B` is the open unit ball. `∂⁻ₓL(t, x(t))` is `dhSubdiff` of the `EReal` coercion of `L t`.
Weak\* compactness is compactness in `WeakDual ℝ E`. The support function is `EReal`-valued; the
integrand `s(v, ∂⁻ₓL(t, x(t)))` is finite for a.e. `t`, and the conclusion asserts that its real
part is integrable on `I` and that its integral equals `s(v, ∫_I ∂⁻ₓL(t, x(t))dt)`. -/
theorem theorem_A_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (I : Set ℝ) (hI : IsClosed I) (hIne : I.Nonempty)
    (x : ℝ → E) (hx : @NullMeasurable ℝ E _ (borel E) x (volume.restrict I)) (L : ℝ → E → ℝ)
    (hLi : ∀ z : E, NullMeasurable (fun t => L t z) (volume.restrict I))
    (hLii : ∃ ε > 0, ∃ k : ℝ → ℝ, IntegrableOn k I ∧ ∀ t ∈ I, ∀ y ∈ Metric.ball (x t) ε,
      ∀ z ∈ Metric.ball (x t) ε, |L t y - L t z| ≤ k t * ‖y - z‖)
    (hnorm : @Measurable (ℝ × E) ℝ
      (MeasurableSpace.prod (volume : Measure ℝ).toOuterMeasure.caratheodory (borel E)) _
      ((I ×ˢ (univ : Set E)).indicator (Function.uncurry L)))
    (hlsc : ∀ t ∈ I, LowerSemicontinuous (L t))
    (hne : ∀ᵐ t ∂(volume.restrict I), (dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)).Nonempty) :
    (∃ f : ℝ → E →L[ℝ] ℝ,
      (∀ᵐ t ∂(volume.restrict I), f t ∈ dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) ∧
      ∃ z, IsGelfandIntegral f I z) ∧
    IsCompact (StrongDual.toWeakDual ''
      gelfandSetIntegral (fun t => dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) I) ∧
    Convex ℝ (gelfandSetIntegral (fun t => dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) I) ∧
    ∀ v : E,
      IntegrableOn
        (fun t => (supportFn (dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) v).toReal) I ∧
      supportFn (gelfandSetIntegral (fun t => dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) I) v =
        (((∫ t in I,
          (supportFn (dhSubdiff (fun z => ((L t z : ℝ) : EReal)) (x t)) v).toReal) : ℝ) : EReal) := by sorry

end InfHorizonVP
