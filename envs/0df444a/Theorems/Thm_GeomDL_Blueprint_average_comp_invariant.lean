-- Prove2me | Theorems.Thm_GeomDL_Blueprint_average_comp_invariant
-- name    : GeomDL.Blueprint.average_comp_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:23.28191+00:00
-- url     : https://prove2.me/theorems/7c3ce62b-76fb-4a66-bf70-bcfbc42e12e4
-- title:
--   §3.5, p. 27 — the G-average A is invariant, so A ∘ U is G-invariant for every equivariant U
-- statement:
--   Let a group $\mathfrak G$ act on a finite domain $\Omega$, and let $\mu$ be a finite, nonzero, right-invariant measure on $\mathfrak G$ (for example the Haar measure of a compact group). Let
--   $$A x = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} (\mathfrak g . x)\, \mathrm d\mu(\mathfrak g)$$
--   be the $\mathfrak G$-average of a real signal $x : \Omega \to \mathbb R$. Then
--
--   1. $A$ is $\mathfrak G$-invariant: $A(\mathfrak h . x) = A(x)$ for all $\mathfrak h \in \mathfrak G$ and all $x$;
--   2. for every $\mathfrak G$-equivariant $U : X(\Omega, C) \to X(\Omega, \mathbb R)$, the composite $A \circ U$ is $\mathfrak G$-invariant.
--
--   Composing equivariant layers with a group average is the book's general recipe for invariant functions.
--
--   **Formalization Note** The book writes $A \circ U : X(\Omega, C) \to C''$, i.e. it reads off a value; here $A \circ U$ returns the averaged signal, and any further read-out of it stays invariant. The page does not state the invariance of $\mu$ it needs; right invariance ($\mu(Eh) = \mu(E)$) is the hypothesis under which the substitution $\mathfrak g \mapsto \mathfrak g\mathfrak h$ leaves the integral unchanged, and the Haar measure of a compact group, which the book names, has it. Measurability is ensured by assuming the inversion and the action measurable, with the discrete σ-algebra on $\Omega$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.5, p. 27, "This simple property allows us to define a very general family of G-invariants ..."; side-note p. 27 (Haar measure)

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

open MeasureTheory

/-- Bronstein et al., §3.5, p. 27: "This simple property allows us to define a very general family
of G-invariants, by composing U with the group averages A ∘ U." For a finite domain `Ω`, a finite
nonzero right-invariant measure `μ` on `G` (the Haar measure of a compact group is one), and the
`G`-average `A x = (1/μ(G)) ∫ (g.x) dμ(g)`:
1. `A` is `G`-invariant: `A(h.x) = A(x)` for all `h` and `x`;
2. for every `G`-equivariant `U : X(Ω, C) → X(Ω, ℝ)`, the composite `A ∘ U` is `G`-invariant. -/
theorem average_comp_invariant {G Ω C : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [MeasurableInv G] [MeasurableSMul G Ω]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) :
    (∀ (h : G) (x : Ω → ℝ), groupAverage μ (act h x) = groupAverage μ x) ∧
    (∀ U : (Ω → C) → (Ω → ℝ), IsEquivariant (G := G) U →
      IsInvariant (G := G) (groupAverage μ ∘ U)) := by sorry

end GeomDL.Blueprint
