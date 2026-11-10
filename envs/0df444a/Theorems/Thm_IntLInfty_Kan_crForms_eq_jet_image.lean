-- Prove2me | Theorems.Thm_IntLInfty_Kan_crForms_eq_jet_image
-- name    : IntLInfty.Kan.crForms_eq_jet_image
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:21.91511+00:00
-- url     : https://prove2.me/theorems/b032357a-19d5-4f45-b385-096065ff2fe5
-- title:
--   The Banach spaces $\Omega^n_{C^r}(\Delta^m)$ and $\Omega^n_{\mathrm{closed}}(\Delta^m)$ are exactly the jets of $C^r$ forms
-- statement:
--   Let $r\ge 1$. The closed linear span of the $C^r$ jets $j^r(\omega)=(j^r\omega, j^r d\omega)$ of $n$-forms $\omega$ on the simplex $\Delta^m$ with $\omega, d\omega$ of class $C^r$ adds nothing: it is the set of such jets itself, and likewise for closed forms:
--   $$\Omega^n_{C^r}(\Delta^m)=\{\,j^r(\omega) : \omega\in\Omega^n,\ \omega,d\omega\in C^r\,\},\qquad \Omega^n_{\mathrm{closed}}(\Delta^m)=\{\,j^r(\omega) : \omega\in\Omega^n,\ \omega,d\omega\in C^r,\ d\omega=0 \text{ on } \Delta^m\,\}.$$
--   (The jet image is a linear subspace, and it is closed because a $C^r$-convergent sequence of jets on the convex body $\Delta^m$ is the jet of a $C^r$ limit form.)
--
--   Role: every element of these Banach spaces has a representative form, so face maps, $d$ and wedge products can be computed on representatives.
-- source:
--   Henriques, Integrating L-infinity algebras, arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, Convention 5.1 and Section 5 (Banach spaces of C^r forms on the simplex used in the proof of Theorem 5.10, p. 16)

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

namespace IntLInfty.Kan

theorem crForms_eq_jet_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} ∧
      (CrClosed r m n : Set (Jet r m × Jet r m)) =
        jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by sorry

end IntLInfty.Kan
