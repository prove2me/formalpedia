-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
-- name    : ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/3054d456-4e6d-5692-a913-f9d04dc4a2c8
-- title:
--   Points of mathbb Z_{(q)} factor through residue fields of places of ℚ̄
-- statement:
--   Fix a natural number $q$ assumed prime, and let $\kappa$ be an algebraically closed field of characteristic $q$ (a `Field` with `CharP κ q` and `IsAlgClosed κ`, in the universe of `Type`). Let `toκ` be any ring homomorphism from the project's ring `DRLevel.R q` — the subring of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $q$, i.e. $\mathbb Z_{(q)}$ — to $\kappa$. The assertion is that there exist: a valuation subring $A$ of $\overline{\mathbb Q}$ (the Lean `AlgebraicClosure ℚ`) such that the image of $q$ in $\overline{\mathbb Q}$ lies in the non-units of $A$, i.e. in the maximal ideal of the local ring $A$; together with proofs, bound existentially so that consumers may supply them as instances, that the residue field of $A$ has characteristic $q$ and is algebraically closed; a ring homomorphism $\rho : \mathbb Z_{(q)} \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structure map $\mathbb Z_{(q)} \to \overline{\mathbb Q}$; and a ring homomorphism $\varphi$ from the residue field of $A$ to $\kappa$ with $\varphi \circ \mathrm{res}_A \circ \rho = \mathrm{to}\kappa$.
--
--   This is the standard statement that every geometric point of $\operatorname{Spec}\mathbb Z_{(q)}$ in characteristic $q$ is induced by a place of $\overline{\mathbb Q}$ above $q$, the residue field of such a place being an algebraic closure of $\mathbb F_q$. It is the device by which reductions modulo a place of $\overline{\mathbb Q}$ are compared with a given characteristic-$q$ geometric fibre, and it is used in the Deligne–Rapoport-level analysis of fibres and charts of the modular curves, for instance in [`ModularCurve.DRLevel.exists_comp_pair_fibre`](thm.html#ModularCurve.DRLevel.exists_comp_pair_fibre) and [`ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin`](thm.html#ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel IsLocalRing

theorem ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : DRLevel.R q →+* κ) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime q)
      (_ : CharP (ResidueField ↥A) q) (_ : IsAlgClosed (ResidueField ↥A))
      (ρ : DRLevel.R q →+* ↥A) (_ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
      (φ : ResidueField ↥A →+* κ), φ.comp ((residue ↥A).comp ρ) = toκ := by sorry
