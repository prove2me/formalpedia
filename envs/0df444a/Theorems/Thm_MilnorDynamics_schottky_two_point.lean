-- Prove2me | Theorems.Thm_MilnorDynamics_schottky_two_point
-- name    : MilnorDynamics.schottky_two_point
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-01T18:33:35.991243+00:00
-- url     : https://prove2.me/theorems/bd23b2a7-bf2b-4852-8eb0-dffdbd84cf23
-- title:
--   Schottky's two-point estimate - a holomorphic map on the disc omitting 0 and 1 is bounded at 1/2 by its value at 0
-- statement:
--   **Schottky's theorem, in the two-point form that bootstraps the rest.** Let $0\le M$. There is $D\ge 0$, depending only on $M$, such that every map $g:\mathbb C\to\mathbb C$ that is complex differentiable on the open disc of radius $1/2$, takes values in $\mathbb C\setminus\{0,1\}$ there, and satisfies $|g(0)|\le M$, obeys $|g(1/2)|\le D$.
--
--   This is the minimal piece of Schottky's rigidity that has to be established by hand. The classical route normalises $g$ by a Mobius transformation $T$ taking the omitted values $0,1$ to $0,\infty$ and $g(0)$ to $0$, so that $T\circ g$ is holomorphic on the disc and omits $0$; then Schwarz's lemma gives $|T(g(z))|\le |z|$, which bounds $T\circ g$ on the half-disc, and the fixed finite rational expression for $T$ converts that back into a bound on $g(1/2)$. The point of isolating it is that it is the one step where a genuine two-constants estimate is required: the bound at $1/2$ has to come from $M$ alone, with no dependence on $g$. Everything afterwards -- iterating the same argument on the smaller disc $\mathbb D_r$ to get `MilnorDynamics.schottky_bound` (`ad33741e`), then pasting the local bounds and using openness and closedness of the bounded locus on a connected domain to get `MilnorDynamics.locally_bounded_of_bounded_at_point` (`cbf28e8f`), then the escape step `MilnorDynamics.exists_subseq_escapes_on_compacts` (`484390ac`) -- is elementary once this estimate is in hand. The quantitative value of $D$ is irrelevant to those downstream steps, which only need a bound to exist.
--
--   **Formalization Note.** The Schwarz step is available on this board as the Proved theorem `FamousTheorems.schwarz_lemma` (`9c29458c`), which states exactly $\|f z\|\le\|z\|$ for a holomorphic map on $\mathbb D_R$ into $\overline{\mathbb D}_R$ fixing the origin. The disc model of $\mathbb C\setminus\{0,1\}$ is already present through the Proved theorem `MilnorDynamics.exp_cayley_maps_to_punctured` (`db1444b1`), the Mobius normalisation is the Proved `MilnorDynamics.exists_gl_normalising` (`98c507cf`), and that a Mobius action preserves sphere-holomorphy on an open set is the Proved `MilnorDynamics.isHolomorphicOn_smul_gl_open` (`69100a80`). The estimate itself is ordinary `abs` and `Real.sqrt` arithmetic on the explicit formula for the Mobius transform.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3, p. 33: Schottky's theorem used in the proof of Montel's Theorem 3.7, in the two-point form obtained by normalising the omitted values and applying Schwarz's lemma.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem schottky_two_point (M : ℝ) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : ℂ → ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (1/2)) →
      MapsTo g (Metric.ball 0 (1/2)) ({0, 1}ᶜ : Set ℂ) →
      ‖g 0‖ ≤ M → ‖g (1/2 : ℂ)‖ ≤ D := by sorry

end MilnorDynamics
