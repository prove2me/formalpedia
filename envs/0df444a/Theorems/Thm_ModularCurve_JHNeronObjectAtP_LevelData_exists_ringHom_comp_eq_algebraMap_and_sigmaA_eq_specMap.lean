-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/80f5d967-9378-5d84-afa7-69dfa54710da
-- title:
--   The base point of a level datum is Spec of a ring map
-- statement:
--   Fix a natural number $p$ and a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a proof that $p \mid M$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $\Lambda$ be a level datum `JHNeronObjectAtP.LevelData p M H hpM A`, i.e. a structure consisting of a morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` together with the compatibility `barPt A ≫ σA = genPt p`, a scheme $X$ with a morphism $f$ to `base p`, a relative group law `L` for $f$ over the ring `baseRing p` (the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$), a bijection between $J_H$ at level $M/p$ for the induced subgroup and the sections of $f$ over `genPt p`, and a bijection between $\mathrm{Pic}^0$ of the reduction curve over the residue field of $A$ and the sections of $f$ over `resPt A ≫ σA`. The assertion is that there exists a ring homomorphism $\rho \colon$ `baseRing p` $\to A$ such that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ equals the structure map `baseRing p` $\to \overline{\mathbb{Q}}$, and such that $\sigma_A = \operatorname{Spec}(\rho)$. Primality of $p$ is not assumed, and the proof uses only the fields $\sigma_A$ and its compatibility from $\Lambda$.
--
--   This records that the base point of a level datum at a place of $\overline{\mathbb{Q}}$ is affine in the strongest sense: it is induced by a ring homomorphism $\mathbb{Z}_{(p)} \to A$ compatible with the embedding $A \subseteq \overline{\mathbb{Q}}$. The resulting triple $(\rho, \text{compatibility}, \sigma_A = \operatorname{Spec} \rho)$ is what the later specialisation arguments for the Néron object of $J_H(M)$ at $p$ — the base-change and torus-fibre statements and the bound on inertia invariants of the torsion — take as input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
    (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A) :
    ∃ ρ : baseRing p →+* ↥A, A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ) ∧ Λ.σA = Spec.map (CommRingCat.ofHom ρ) := by sorry
