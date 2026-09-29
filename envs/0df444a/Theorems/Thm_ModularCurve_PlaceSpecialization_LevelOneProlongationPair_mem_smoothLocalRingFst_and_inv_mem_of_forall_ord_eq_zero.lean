-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/ebe48f73-fc87-5030-9ead-7adddad2efb6
-- title:
--   R₁-units with no zeros over v are units at v
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing at $(j, j_q)$), a proof `hKr` that the reduction of $\Phi$ modulo $q$ is $(C(X)^q - X)(C(X) - X^q)$, and integrality proofs $h\alpha$, $h\beta$ for the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$. Let $P$ be a place specialisation for these data, $R$ a level-one prolongation pair for $P$ (with its two regular prolongations $R_1$, $R_2$ of $A$ in $\overline{\mathbb{Q}}$-modular function field of level $1\cdot q$, with residue fields in the level-one modular function field over the residue field of $A$), and $v$ a place of $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$. Assume $v = P.\mathrm{redFst}\,W_0$ for at least one place $W_0$ of the level-$(1\cdot q)$ function field over $\overline{\mathbb{Q}}$ of strict type one, i.e. with $\mathrm{Frob}$ taking $P.\mathrm{redFst}\,W_0$ to $P.\mathrm{redSnd}\,W_0$ while $\mathrm{Frob}^2(P.\mathrm{redFst}\,W_0) \neq P.\mathrm{redFst}\,W_0$ (here $\mathrm{redFst}$ is restriction of the place along $\overline{\alpha}$ followed by the specialisation map `sp` of $P$). Let $f$ be an element of the level-$(1\cdot q)$ function field lying in the integers of $R_1$ with nonzero $R_1$-residue, and suppose $W.\mathrm{ord}\,f = 0$ for every strict-type-one place $W$ with $P.\mathrm{redFst}\,W = v$. Then both $f$ and $f^{-1}$ lie in $R.\mathrm{smoothLocalRingFst}\,v$, the intersection of the integers of $R_1$ with the valuation subrings of all strict-type-one places $W$ satisfying $P.\mathrm{redFst}\,W = v$.
--
--   This is the Hartogs-type statement at a smooth point of the first component of the level-one model: an element which is a unit for the prolongation $R_1$ and has neither zero nor pole at the strict-type-one points lying over $v$ is a unit of the local ring of the model at $v$, zeros and poles at places reducing to the other component being permitted. It is used in the value law for residues on the model, in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : ∃ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.IsStrictTypeOne W ∧ P.redFst W = v)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hdisc : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne W → P.redFst W = v → W.ord f = 0) :
    f ∈ R.smoothLocalRingFst v ∧ f⁻¹ ∈ R.smoothLocalRingFst v := by sorry
