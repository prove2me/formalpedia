-- Prove2me | Theorems.Thm_OAI_Paper256_positive_map_resolvent_isUnit
-- name    : OAI.Paper256.positive_map_resolvent_isUnit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:23:35.568989+00:00
-- url     : https://prove2.me/theorems/3974cf91-7d5b-470f-8a7f-6253dd7b2235
-- title:
--   Invertibility of $zI-B-\Phi\big((zI-A)^{-1}\big)$ for positive maps $\Phi$ and non-real $z$
-- statement:
--   Let $n,m\ge0$ be integers, let $A\in\mathbb{C}^{n\times n}$ and $B\in\mathbb{C}^{m\times m}$ be Hermitian matrices, and let $\Phi:\mathbb{C}^{n\times n}\to\mathbb{C}^{m\times m}$ be a $\mathbb{C}$-linear map such that
--
--   1. $\Phi$ commutes with adjoints: $\Phi(M)^*=\Phi(M^*)$ for every $M\in\mathbb{C}^{n\times n}$;
--   2. $\Phi$ is positive: $\Phi(M)\succeq0$ whenever $M\succeq0$ (here $M\succeq0$ means $M$ is Hermitian positive semidefinite).
--
--   Then for every complex number $z$ with $\operatorname{Im}z\neq0$ the $m\times m$ matrix
--   $$
--   zI_m-B-\Phi\big((zI_n-A)^{-1}\big)
--   $$
--   is invertible. (The inverse $(zI_n-A)^{-1}$ exists because the eigenvalues of the Hermitian matrix $A$ are real.)
--
--   In words: for a positive, adjoint-preserving $\Phi$, the matrix-valued function $z\mapsto zI_m-B-\Phi\big((zI_n-A)^{-1}\big)$ is never singular off the real axis. Applied to real symmetric $A,B$ and the positive map $\Phi=\varphi_y$, it shows that determinants of the form $\det\big(zI-B-\varphi_y((zI-A)^{-1})\big)$ have no non-real zeros, which is the key step in proving that a determinantal polynomial built from $\varphi_y$ is hyperbolic.
--
--   **Formalization Note** Invertibility is stated as `IsUnit`. The inverse is Mathlib's matrix inverse `Matrix.inv`, a total function that returns $0$ on singular matrices; since $zI_n-A$ is invertible here, it is the usual inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/MatrixResolvent.lean#L49-L81

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates

open OAI OAI.Paper256
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

theorem OAI.Paper256.positive_map_resolvent_isUnit {n m : ℕ} (A : Mat n ℂ) (B : Mat m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Φ : Mat n ℂ →ₗ[ℂ] Mat m ℂ)
    (hΦstar : ∀ X, (Φ X)ᴴ = Φ Xᴴ)
    (hΦpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (z • (1 : Mat m ℂ) - B - Φ ((z • (1 : Mat n ℂ) - A)⁻¹)) := by sorry
