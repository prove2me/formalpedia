-- Prove2me | Theorems.Thm_Hatcher_fundamentalGroup_map_bijective_of_homotopyEquiv
-- name    : Hatcher.fundamentalGroup_map_bijective_of_homotopyEquiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-14T12:43:03.908075+00:00
-- url     : https://prove2.me/theorems/d598209f-17b1-4bcc-a15e-7f59f964dbde
-- title:
--   Hatcher Proposition 1.18 — a homotopy equivalence induces an isomorphism on π₁ at every basepoint
-- statement:
--   Let $\varphi \colon X \to Y$ be a homotopy equivalence, that is, a map admitting $\psi \colon Y \to X$ with $\psi\varphi \simeq \mathrm{id}_X$ and $\varphi\psi \simeq \mathrm{id}_Y$. Then for **every** $x_0 \in X$ the induced homomorphism
--
--   $$\varphi_* \colon \pi_1(X, x_0) \longrightarrow \pi_1\bigl(Y, \varphi(x_0)\bigr)$$
--
--   is an isomorphism.
--
--   **Role.** The force of the statement is the absence of any hypothesis on the basepoint. The homotopies witnessing the equivalence need not fix $x_0$, so the composites they are homotopic to land at moved basepoints; the change-of-basepoint lemma is what repairs that, after which a two-out-of-three argument on the three induced homomorphisms gives the result.
--
--   **Formalization note.** Isomorphism is rendered as bijectivity of the induced homomorphism, which for a group homomorphism is equivalent and avoids producing an isomorphism object. The homotopy equivalence is taken as the structure carrying the two maps and the two homotopies.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Section 1.1, p. 37, Proposition 1.18: "If phi : X -> Y is a homotopy equivalence, then the induced homomorphism phi_* : pi_1(X, x0) -> pi_1(Y, phi(x0)) is an isomorphism for all x0 in X." PROVENANCE: isomorphism is rendered as bijectivity of the induced homomorphism.

import Mathlib

namespace Hatcher

open ContinuousMap FundamentalGroup

theorem fundamentalGroup_map_bijective_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x₀) := by
  sorry

end Hatcher
