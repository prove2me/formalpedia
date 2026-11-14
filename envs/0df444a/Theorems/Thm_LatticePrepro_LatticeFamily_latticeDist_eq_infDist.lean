-- Prove2me | Theorems.Thm_LatticePrepro_LatticeFamily_latticeDist_eq_infDist
-- name    : LatticePrepro.LatticeFamily.latticeDist_eq_infDist
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:23.386305+00:00
-- url     : https://prove2.me/theorems/81b62391-bfe7-41fc-acf1-671e341274ae
-- title:
--   Definition 3.1 in Mathlib terms — $\operatorname{dist}_p(t_x,\Lambda)$ is Mathlib's infimum distance in $\ell_p^M$
-- statement:
--   Let $(\Lambda,(t_x)_{x\in X})$ be a lattice family with $\Lambda\subseteq\mathbb Z^M$, let $p$ be a norm exponent (a real $p\ge1$ or $p=\infty$), and let $x$ be an instance. Write $\ell_p^M$ for $\mathbb R^M$ with the $\ell_p$ norm, as Mathlib's `PiLp p (fun _ : M => ℝ)`, and $\Lambda_{\mathbb R}\subseteq\mathbb R^M$ for the image of $\Lambda$ under the cast $\mathbb Z^M\to\mathbb R^M$. Then
--   $$\operatorname{dist}_p(t_x,\Lambda)=\operatorname{infDist}_{\ell_p^M}\bigl(t_x,\Lambda_{\mathbb R}\bigr)=\inf_{u\in\Lambda_{\mathbb R}}\|t_x-u\|_{\ell_p^M}.$$
--   The left side is the project's lattice distance (`latticeDist`, the infimum of $\|t_x-v\|_p$ over $v\in\Lambda$, computed with the project's own $\ell_p$ norm $\bigl(\sum_i|v_i|^p\bigr)^{1/p}$ or $\sup_i|v_i|$). The right side is Mathlib's `Metric.infDist` from the point $t_x$ to the set $\Lambda_{\mathbb R}$, both viewed in the normed space $\ell_p^M$.
--
--   This certifies that the distance in the final lattice theorems (Theorem 5.1) and in the search test (Lemma 5.2) is the standard distance of Definition 3.1, $\operatorname{dist}_p(t,\mathcal L)=\min_{v\in\mathcal L}\|t-v\|_p$, expressed with Mathlib's infimum distance in the $\ell_p$ space.
--
--   **Formalization Note.** The exponent enters Mathlib through `PNorm.toENNReal` ($p\mapsto p$, $\infty\mapsto\top$), and vectors are moved into `PiLp` with `WithLp.toLp`. $\Lambda_{\mathbb R}$ is `LatticeFamily.realLattice`, and the target is cast with `LatticeFamily.toReal`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.1 (\label{def:code-lattice-distances}); Lean: LatticePrepro/Lattices/Mathlib.lean, LatticePrepro.LatticeFamily.latticeDist_eq_infDist

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib

open LatticePrepro
open scoped ENNReal
open WithLp
open LatticePrepro.LatticeFamily
variable {X : Type} (Λ : LatticeFamily X)

theorem LatticePrepro.LatticeFamily.latticeDist_eq_infDist (pn : PNorm) (x : X) :
    Λ.latticeDist pn x =
      Metric.infDist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ))) := by sorry
