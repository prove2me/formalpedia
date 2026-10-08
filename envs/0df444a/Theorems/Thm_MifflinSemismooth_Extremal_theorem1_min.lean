-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_theorem1_min
-- name    : MifflinSemismooth.Extremal.theorem1_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:35:12.105993+00:00
-- url     : https://prove2.me/theorems/c7941ab6-d907-4757-8d71-a0f326bb537f
-- title:
--   Theorem 1, pp. 7–8, min form — E is Lipschitz, ∂E(x) = conv{∂ₓf(x,u) : u ∈ A(x)}, E′ = −E⁰(x;−d) = min over active gradients
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open, $T$ a topological space, $U\subseteq T$ sequentially compact, $f:\mathbb R^n\times T\to\mathbb R$ and $E:\mathbb R^n\to\mathbb R$. Assume:
--
--   1. (a) $f$ is continuous on $B\times U$;
--   2. (b) $f(\cdot,u)$ is Lipschitz on $B$, uniformly in $u\in U$;
--   3. (c) $\partial_x f$ is upper semicontinuous on $B\times U$;
--   4. (d′) $E(x)=\min\{f(x,u):u\in U\}$ for every $x\in B$;
--   5. (e′) $f'_x(x,u;d)$ exists and equals $-f^0_x(x,u;-d)$ for all $x\in B$, $u\in U$, $d$.
--
--   Then $E$ is Lipschitz on $B$, and for each $x\in B$, with $A(x)=\{u\in U:E(x)=f(x,u)\}$,
--
--   $$\partial E(x)=\operatorname{conv}\bigcup_{u\in A(x)}\partial_x f(x,u),$$
--
--   and for each $d\in\mathbb R^n$ the directional derivative $E'(x;d)$ exists and
--
--   $$E'(x;d)=-E^0(x;-d)=\min\{\langle g,d\rangle:\ g\in\partial_x f(x,u),\ u\in A(x)\}.$$
--
--   This is the min-function counterpart of the max form of Theorem 1.
--
--   **Formalization Note.** "min" is `IsLeast` (attained); "conv" is the plain convex hull of the union. The page's alternative "(d′) and (e′)" is read as holding on all of $B$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), pp. 7–8, §3, Theorem 1 (min form, hypotheses (a)–(c), (d'), (e'))

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Theorem 1, pp. 7–8, min form: under (a), (b), (c), (d'), (e'), `E` is
Lipschitz on `B`, and for each `x ∈ B`, `∂E(x) = conv {∂ₓf(x, u) : u ∈ A(x)}` and, for each `d`,
`E'(x; d) = -E⁰(x; -d) = min [⟨g, d⟩ : g ∈ ∂ₓf(x, u), u ∈ A(x)]`. -/
theorem theorem1_min {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hb : HypB B U f) (hc : HypC B U f) (hd' : HypD' B U f E)
    (he' : HypE' B U f) :
    (∃ K : NNReal, LipschitzOnWith K E B) ∧
    ∀ x ∈ B,
      genGrad E x = convexHull ℝ (⋃ u ∈ activeSet U f E x, partialGenGrad f x u) ∧
      ∀ d, HasDirDeriv E x d (-(ClarkeGradients.Shared.genDirDeriv E x (-d))) ∧
        IsLeast {r | ∃ u ∈ activeSet U f E x, ∃ g ∈ partialGenGrad f x u, r = inner ℝ g d}
          (-(ClarkeGradients.Shared.genDirDeriv E x (-d))) := by sorry

end MifflinSemismooth.Extremal
