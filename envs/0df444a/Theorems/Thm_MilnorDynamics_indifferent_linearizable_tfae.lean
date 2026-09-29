-- Prove2me | Theorems.Thm_MilnorDynamics_indifferent_linearizable_tfae
-- name    : MilnorDynamics.indifferent_linearizable_tfae
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T11:08:01.312987+00:00
-- url     : https://prove2.me/theorems/4d11515f-72ed-434e-b71d-420f01cce417
-- title:
--   Lemma 11.1 — for an indifferent fixed point: linearizable ⇔ Fatou ⇔ Siegel disk
-- statement:
--   Let $f$ be a rational function of degree $\ge2$ with a fixed point $z_0$ which is indifferent, $|f'(z_0)|=|\lambda|=1$. Then the following three conditions are equivalent:
--   - $f$ is locally linearizable around $z_0$;
--   - $z_0$ belongs to the Fatou set $\hat{\mathbb C}\smallsetminus J(f)$;
--   - the connected component $U$ of the Fatou set containing $z_0$ is conformally isomorphic to the unit disk under an isomorphism which conjugates $f$ on $U$ to multiplication by $\lambda$ on the disk.
--
--   **Formalization Note** The equivalence of three statements is stated as $(1\Leftrightarrow2)\wedge(2\Leftrightarrow3)$. The multiplier at $\infty$ is computed in the chart $1/z$. The conformal isomorphism of (3) is encoded by its inverse $h$: a holomorphic injective map of the unit disk onto $U$ with $h(0)=z_0$ and $f\circ h=h\circ(\lambda\cdot)$; a holomorphic bijection is automatically biholomorphic.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §11, p. 125, Lemma 11.1

import Mathlib
import Definitions.Def_MilnorDynamics_Linearization

open scoped OnePoint Topology
open Filter Set MeasureTheory

namespace MilnorDynamics

theorem indifferent_linearizable_tfae (f : RationalMap) (hf : 2 ≤ f.degree)
    (p : OnePoint ℂ) (hp : f.toFun p = p) (hind : ‖multiplier f.toFun p‖ = 1) :
    (IsLinearizableAt f.toFun p (multiplier f.toFun p) ↔ p ∈ fatouSet f.toFun) ∧
      (p ∈ fatouSet f.toFun ↔
        ∃ h : ℂ → OnePoint ℂ, IsHolomorphicOn (Metric.ball 0 1) h ∧ InjOn h (Metric.ball 0 1) ∧
          h 0 = p ∧ h '' Metric.ball 0 1 = connectedComponentIn (fatouSet f.toFun) p ∧
          ∀ w ∈ Metric.ball (0 : ℂ) 1, f.toFun (h w) = h (multiplier f.toFun p * w)) := by sorry

end MilnorDynamics
