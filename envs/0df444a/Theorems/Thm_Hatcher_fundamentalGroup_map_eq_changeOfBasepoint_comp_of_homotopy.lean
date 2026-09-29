-- Prove2me | Theorems.Thm_Hatcher_fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy
-- name    : Hatcher.fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-14T12:42:59.690649+00:00
-- url     : https://prove2.me/theorems/cdc3c70c-6440-4a80-89da-5a1eae845fde
-- title:
--   Hatcher Lemma 1.19 — the ends of a homotopy induce maps on π₁ differing by change of basepoint
-- statement:
--   Let $\varphi_t \colon X \to Y$ be a homotopy, from $\varphi_0$ to $\varphi_1$, and let $x_0 \in X$. The basepoint traces a path
--
--   $$h(t) = \varphi_t(x_0), \qquad h(0) = \varphi_0(x_0), \quad h(1) = \varphi_1(x_0),$$
--
--   and transporting along $h$ gives an isomorphism $\beta_h$ between the fundamental groups of $Y$ at its two endpoints. The claim is that the two homomorphisms induced on $\pi_1$ by the ends of the homotopy differ by exactly that transport:
--
--   $$\varphi_{1*} \;=\; \beta_h \circ \varphi_{0*} \colon \ \pi_1(X, x_0) \longrightarrow \pi_1\bigl(Y, \varphi_1(x_0)\bigr).$$
--
--   **Role.** A homotopy need not fix the basepoint, so the maps it connects induce homomorphisms into fundamental groups at *different* points of $Y$, and they cannot be compared directly. This says the only discrepancy is the change of basepoint along the path the basepoint travels — which is what allows basepoint conditions to be dropped from statements about homotopy equivalences.
--
--   **Formalization note.** Hatcher writes the conclusion as $\varphi_{0*} = \beta_h \varphi_{1*}$, with his $\beta_h$ running from the fundamental group at $h(1)$ to the one at $h(0)$. The transport used here runs the other way, from $h(0)$ to $h(1)$, so the equation is stated in the transposed form above; the content is the same. Mathlib supplies the path a homotopy's basepoint traces, and the isomorphism obtained by transporting along a path. The homotopy enters as *data* — a chosen homotopy, not the assertion that one exists — and it is not required to fix the basepoint; that freedom is the whole point of the lemma.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Section 1.1, p. 37, Lemma 1.19: "If phi_t : X -> Y is a homotopy and h is the path phi_t(x0) formed by the images of a basepoint x0 in X, then the three maps in the diagram at the right satisfy phi_{0*} = beta_h phi_{1*}." PROVENANCE: stated here in the transposed form, because the change-of-basepoint isomorphism available in Mathlib runs from the start of the path to its end, the opposite of Hatcher's beta_h; the content is unchanged.

import Mathlib

namespace Hatcher

open CategoryTheory ContinuousMap FundamentalGroup FundamentalGroupoidFunctor

theorem fundamentalGroup_map_eq_changeOfBasepoint_comp_of_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {φ₀ φ₁ : C(X, Y)} (H : ContinuousMap.Homotopy φ₀ φ₁) (x₀ : X) :
    FundamentalGroup.map φ₁ x₀
      = (fundamentalGroupMulEquivOfPath (H.evalAt x₀)).toMonoidHom.comp
          (FundamentalGroup.map φ₀ x₀) := by
  sorry

end Hatcher
