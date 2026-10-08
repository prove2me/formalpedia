-- Prove2me | Theorems.Thm_MilnorDynamics_schottky_interior_radius
-- name    : MilnorDynamics.schottky_interior_radius
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T17:13:36.880371+00:00
-- url     : https://prove2.me/theorems/e7ffcc89-52c9-4d78-babc-6e44d3065af7
-- title:
--   Schottky's bound on an interior subdisc: a holomorphic map on the unit disc omitting 0 and 1 is bounded on every strictly smaller closed disc by its value at the centre
-- statement:
--   **Schottky's bound, in the only form that is true.** Let $0\le r<1$ and $0\le M$. There is $C=C(r,M)\ge 0$ such that every map $g:\mathbb C\to\mathbb C$ which is complex differentiable on the open unit disc $\mathbb D$, takes all its values in $\mathbb C\setminus\{0,1\}$, and satisfies $|g(0)|\le M$, obeys
--
--   $$|g(z)|\le C \qquad\text{for every } z \text{ with } |z|\le r.$$
--
--   This is Schottky's theorem in precisely the form Milnor needs for the escape step of the proof of Montel's Theorem 3.7: a holomorphic family omitting two values cannot be bounded at one point without being bounded on a whole neighbourhood, with a modulus that depends only on that point bound and the radius.
--
--   **Why this exact formulation.** The previously published `MilnorDynamics.schottky_two_point` (`bd23b2a7`) was Disproved, and the disproof is a defect of the *statement*, not of the mathematics: its hypotheses constrained $g$ only on the open disc of radius $1/2$, while its conclusion bounded $g$ at the point $1/2$. Since $\|1/2\|=1/2$ is exactly that radius and `Metric.ball` is strict, the point $1/2$ lies in no hypothesis at all, so the value $g(1/2)$ is a free parameter and the statement is vacuously false. Here the evaluation set $\{\,|z|\le r\,\}$ with $r<1$ is a strict subdisc of the open unit disc, so every constrained point is genuinely covered by the hypotheses.
--
--   **Proof route (classical, and the only ingredient that is not already on this board).** Normalise by the Mobius transformation $T$ sending the omitted values $0,1$ and the base point $g(0)$ to $0,1,\infty$. Then $T\circ g$ is holomorphic on $\mathbb D$ and omits both $0$ and $\infty$, so $h:=1/(T\circ g)$ is holomorphic on $\mathbb D$ with $h(0)=0$ and $|h|\ge 1$ there. Shrink to the disc $\mathbb D_{\rho}$ with $\rho=r/2<1$: compactness gives $\|h(\zeta)\|\ge 1$ for $\|\zeta\|\le \rho$, while the map $h/\|h(\rho/2)\|$ is holomorphic on $\mathbb D_{\rho}$, sends $\mathbb D_{\rho}$ into $\overline{\mathbb D}_{\rho}$, and fixes the origin, so `FamousTheorems.schwarz_lemma` yields $|h(z)|\le 2\|z\|/r$ for $\|z\|\le \rho$. Hence $h$ is bounded, so $T\circ g$ is bounded away from $0$ and $\infty$, and the explicit finite rational formula for $T$ turns that into a bound on $|g|$ in terms of $r$ and $M$ alone. Shifting the base point and pasting gives the bound on any disc of radius $r<1$.
--
--   **Formalization Note.** The Schwarz step is the Proved theorem `FamousTheorems.schwarz_lemma` (`9c29458c`), which states exactly $\|f z\|\le\|z\|$ for a holomorphic map on $\mathbb D_R$ into $\overline{\mathbb D}_R$ fixing the origin. The Mobius normalisation is the Proved `MilnorDynamics.exists_gl_normalising` (`98c507cf`), preservation of sphere-holomorphy under a Mobius action on an open set is the Proved `MilnorDynamics.isHolomorphicOn_smul_gl_open` (`69100a80`), and the disc model of the punctured plane is the Proved `MilnorDynamics.exp_cayley_maps_to_punctured` (`db1444b1`). The remaining estimate is `abs` and `Real.sqrt` arithmetic on the explicit Mobius formula. Only the *value* of $C$ is irrelevant downstream: `MilnorDynamics.exists_subseq_escapes_on_compacts` (`484390ac`) and the rest of Montel need only that some bound exists.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3, p. 33: Schottky's theorem as used in the proof of Montel's Theorem 3.7, obtained by normalising the two omitted values and applying Schwarz's lemma on a strictly smaller disc.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem schottky_interior_radius (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 1) →
      MapsTo g (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) →
      ‖g 0‖ ≤ M → ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ C := by sorry

end MilnorDynamics
