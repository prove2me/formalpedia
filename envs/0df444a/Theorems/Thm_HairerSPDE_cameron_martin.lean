-- Prove2me | Theorems.Thm_HairerSPDE_cameron_martin
-- name    : HairerSPDE.cameron_martin
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:55:08.511909+00:00
-- url     : https://prove2.me/theorems/93b38cc8-5017-44b1-b93c-96ec6f6dde92
-- title:
--   Cameron–Martin theorem: $(T_h)_*\mu \ll \mu \iff h \in H_\mu$
-- statement:
--   **Theorem 4.44 (Cameron–Martin).** Let $B$ be a separable Banach space and let $\mu$ be a centred Gaussian measure on $B$: a Borel probability measure such that the image of $\mu$ under every continuous linear functional $\ell \in B^{*}$ is a real Gaussian law, with $\int_B x\,\mu(dx)=0$. For $h \in B$ let $T_h : B \to B$ be the translation $T_h(x) = x+h$, and let $\|h\|_\mu$ and $H_\mu = \{h : \|h\|_\mu < \infty\}$ be the Cameron–Martin norm and space of $\mu$. Then
--
--   $$ (T_h)_{*}\mu \ \ll\ \mu \qquad \Longleftrightarrow \qquad h \in H_\mu . $$
--
--   That is, the translated measure is absolutely continuous with respect to $\mu$ precisely for the directions of finite Cameron–Martin norm; for every other direction the two measures are not merely inequivalent but mutually singular.
--
--   This is the structural theorem of infinite-dimensional Gaussian analysis. In finite dimensions every direction is admissible, because Lebesgue measure is translation invariant; the theorem says that in infinite dimensions the admissible directions form the proper subspace $H_\mu$, which typically carries measure zero. It is the source of the Girsanov transform for Gaussian noise, of the rate function in Schilder-type large deviation principles, and of the domain of the Malliavin derivative.
--
--   **Formalization Note.** Gaussianity is the hypothesis that the push-forward under each continuous linear functional is a real Gaussian; centredness is the separate hypothesis $\int_B x\,\mu(dx)=0$. The translation is $x\mapsto x+h$ and absolute continuity is the usual "null sets of $\mu$ are null sets of $(T_h)_*\mu$". The space $B$ is assumed complete and second countable, which is the separable Banach hypothesis of the source.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 31, Theorem 4.44 (Cameron–Martin)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem cameron_martin {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) :
    μ.map (fun x ↦ x + h) ≪ μ ↔ cameronMartinNorm μ h ≠ ∞ := by sorry

end HairerSPDE
