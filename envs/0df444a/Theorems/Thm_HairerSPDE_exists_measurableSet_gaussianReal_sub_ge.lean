-- Prove2me | Theorems.Thm_HairerSPDE_exists_measurableSet_gaussianReal_sub_ge
-- name    : HairerSPDE.exists_measurableSet_gaussianReal_sub_ge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:22:52.994425+00:00
-- url     : https://prove2.me/theorems/80e64db4-61a2-4ec7-be3b-792aa923c28f
-- title:
--   $\|\mathcal N(0,1)-\mathcal N(m,1)\|_{\mathrm{TV}} \ge 2-2e^{-m^{2}/8}$
-- statement:
--   **Quantitative separation of a standard Gaussian from its shift.**
--
--   For $m \in \mathbb R$, write $\mathcal N(0,1)$ and $\mathcal N(m,1)$ for the standard Gaussian law and its translate by $m$. Hairer's proof of the converse half of the Cameron–Martin theorem uses the explicit bound
--
--   $$ \bigl\| \mathcal N(0,1) - \mathcal N(m,1) \bigr\|_{\mathrm{TV}} \;\ge\; 2 - 2\exp\!\left(-\frac{m^{2}}{8}\right), $$
--
--   with the normalisation of Section 3.2, in which the total variation distance of two probability measures equals $2\sup_A |\mu(A)-\nu(A)|$ and takes the value $2$ exactly for mutually singular measures. Equivalently, and this is the form claimed here, there is a Borel set $A \subseteq \mathbb R$ with
--
--   $$ \mathcal N(0,1)(A) - \mathcal N(m,1)(A) \;\ge\; 1 - \exp\!\left(-\frac{m^{2}}{8}\right). $$
--
--   The bound is what converts an unboundedly large one-dimensional shift into mutual singularity: if $h \notin H_\mu$ then for every $n$ there is a functional $\ell$ with $C_\mu(\ell,\ell)=1$ and $\ell(h) \ge n$, the two projected laws are $\mathcal N(0,1)$ and $\mathcal N(-\ell(h),1)$, and letting $n \to \infty$ forces total variation distance $2$.
--
--   **Formalization Note.** The statement is given in the equivalent "separating set" form to avoid committing to a particular normalisation of the total variation distance; the case $m = 0$ is included, where the required bound is $0$ and any set works.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 31, proof of Theorem 4.44 (converse direction, explicit total-variation bound); total variation convention of Section 3.2, p. 11

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem exists_measurableSet_gaussianReal_sub_ge (m : ℝ) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      1 - Real.exp (-m ^ 2 / 8)
        ≤ (gaussianReal 0 1 A).toReal - (gaussianReal m 1 A).toReal := by sorry

end HairerSPDE
