-- Prove2me | Theorems.Thm_HairerSPDE_cameronMartinNorm_of_covariance_repr
-- name    : HairerSPDE.cameronMartinNorm_of_covariance_repr
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:18:02.822403+00:00
-- url     : https://prove2.me/theorems/f111d327-86c6-405e-8f81-433c9560700e
-- title:
--   Exercise 4.38: the two descriptions of $\|h\|_\mu$ agree on $\mathring H_\mu$
-- statement:
--   **Consistency of the two definitions of the Cameron–Martin norm (Definition 4.26 and Exercise 4.38).**
--
--   Let $\mu$ be a centred Gaussian measure on a separable Banach space $B$, with covariance form $C_\mu$ on $B^{*}$. Hairer's Definition 4.26 starts from
--
--   $$ \mathring H_\mu = \{\, h \in B : \exists\, h^{*} \in B^{*} \text{ with } C_\mu(h^{*}, \ell) = \ell(h) \ \text{ for all } \ell \in B^{*} \,\}, $$
--
--   and sets $\|h\|_\mu^{2} = C_\mu(h^{*}, h^{*})$ there, while Exercise 4.38 gives the intrinsic description $\|h\|_\mu = \sup\{\ell(h) : C_\mu(\ell,\ell) \le 1\}$. The claim is that the two agree: if $h \in B$ and $h^{*} \in B^{*}$ satisfy $C_\mu(h^{*},\ell) = \ell(h)$ for every $\ell \in B^{*}$, then
--
--   $$ \sup\bigl\{\, \ell(h) : \ell \in B^{*},\ C_\mu(\ell,\ell) \le 1 \,\bigr\} \;=\; \sqrt{C_\mu(h^{*}, h^{*})} . $$
--
--   In particular the right-hand side does not depend on the choice of representer $h^{*}$, which is Hairer's Remark 4.28, and every $h \in \mathring H_\mu$ has finite Cameron–Martin norm.
--
--   This is the compatibility statement that lets the whole theory be developed with the supremum description, which is defined for every $h \in B$ and requires no completion procedure.
--
--   **Formalization Note.** The supremum is taken in the extended non-negative reals and the equality is stated there; the degenerate case $C_\mu(h^{*},h^{*}) = 0$ is included, where both sides are $0$.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 27 Definition 4.26 and p. 29 Exercise 4.38 (eq. (4.12))

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem cameronMartinNorm_of_covariance_repr {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B, covarianceBilinDual μ h' L = L h) :
    cameronMartinNorm μ h = ENNReal.ofReal (Real.sqrt (covarianceBilinDual μ h' h')) := by sorry

end HairerSPDE
