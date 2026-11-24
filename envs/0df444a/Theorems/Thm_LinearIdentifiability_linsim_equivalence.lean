-- Prove2me | Theorems.Thm_LinearIdentifiability_linsim_equivalence
-- name    : LinearIdentifiability.linsim_equivalence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:34:35.536874+00:00
-- url     : https://prove2.me/theorems/836183ff-ef7d-4b7b-be5d-aa2d1b3eb91c
-- title:
--   Appendix B: linear similarity is an equivalence relation
-- statement:
--   Let $\Theta$ be a parameter space and $\theta\mapsto(f_\theta,g_\theta)$ a parameterisation of representations $f_\theta:X\to\mathbb R^M$ and context maps $g_\theta:Y\to\mathbb R^M$. Define $\theta'\sim_L\theta^*$ if there are invertible $M\times M$ matrices $A,B$ with
--
--   $$f_{\theta'}(x)=Af_{\theta^*}(x)\ \ \forall x,\qquad g_{\theta'}(y)=Bg_{\theta^*}(y)\ \ \forall y.$$
--
--   Then $\sim_L$ is an equivalence relation on $\Theta$: it is reflexive, symmetric and transitive.
--
--   This justifies speaking of identifiability up to $\sim_L$ (linear identifiability).
--
--   **Formalization Note** Appendix B writes the argument for $g$ only; the statement covers the relation of Definition 1, which constrains both $f$ and $g$.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 3.2, Definition 1, eq. (3), p. 4; proof in Appendix B, p. 14

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem linsim_equivalence {Θ X Y : Type*} {M : ℕ}
    (f : Θ → X → Fin M → ℝ) (g : Θ → Y → Fin M → ℝ) :
    Equivalence (LinSim f g) := by sorry

end LinearIdentifiability
