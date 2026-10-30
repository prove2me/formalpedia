-- Prove2me | Theorems.Thm_HryniewiczCriterion_local_C2_variational_transport
-- name    : HryniewiczCriterion.local_C2_variational_transport
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:30:30.752987+00:00
-- url     : https://prove2.me/theorems/112fecfe-fd0e-4d25-a435-d469fdd83c21
-- title:
--   Energy and Hamiltonian-direction transport for a locally C2 Hamiltonian orbit
-- statement:
--   Let $H:\mathbb R^4\to\mathbb R$ be $C^2$ at every point of a Hamiltonian trajectory $x(t)$, and let $Y(t)$ be its variational flow with $Y(0)=I$. Then, for every vector $v$ and every time $t$,
--
--   $$dH_{x(t)}(Y(t)v)=dH_{x(0)}(v),\qquad Y(t)X_H(x(0))=X_H(x(t)).$$
--
--   Thus the variational flow preserves energy tangent spaces and transports the Hamiltonian line. Only local $C^2$ regularity along the trajectory is required; no homogeneity or global smoothness assumption is imposed.
-- source:
--   Derived supporting lemma for BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy, https://prove2.me/theorems/eab3aa7c-2cfb-4515-b659-4ccc36142c64. The continuous-path lifting step specializes Mathlib Analysis/Complex/CoveringMap.lean (isCoveringMap_exp); the local C2 Hamiltonian identities adapt Mazecto accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002 without strengthening regularity.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.local_C2_variational_transport (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (HryniewiczCriterion.hamiltonianVectorField H (x t)) t)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) :
    (∀ v t, fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v) ∧
    (∀ t, Y t (HryniewiczCriterion.hamiltonianVectorField H (x 0)) =
      HryniewiczCriterion.hamiltonianVectorField H (x t)) := by sorry
