-- Prove2me | Theorems.Thm_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional
-- name    : ModularCurve.exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/0501eac1-f09b-513c-a8fa-12a02de4e9fd
-- title:
--   Equivariant family with independent residue pairs on X₀(q)
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$, with residue field $\kappa_A$. Let $R_1,R_2$ be regular prolongations of $A$ to $F=$ `modularFunctionFieldBar (1 * q)` (the subfield of $\overline{\mathbb Q}$-coefficient Laurent series generated over $\overline{\mathbb Q}$ by the $q$-expansions generating `modularFunctionFieldFull (1 * q)`) with residue field `modularFunctionFieldFullC (ResidueField A) 1`, i.e. each consists of a valuation subring of $F$ lying over $A$ together with a surjective residue map onto that field whose kernel is the maximal ideal, compatible with reduction on $A$ and non-degenerate after scaling. Assume: (h₁) every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb Q}$-coefficients lies in $F$ belongs to $R_1$, with $R_1$-residue the coefficientwise reduction of $y$; (h₂, h₂') $f\in R_2$ iff $w_q f\in R_1$, and the $R_2$-residue of $f$ is the $R_1$-residue of $w_q f$, where $w_q$ is `frickeInvolutionBar (1 * q)`. Let $S$ be a set of $\mathbb Q$-automorphisms of $\overline{\mathbb Q}$, and $V\subseteq F$ a finite-dimensional $\overline{\mathbb Q}$-subspace, $n=\dim V$. Assume there are $b_1,\dots,b_n\in V$, linearly independent over $\overline{\mathbb Q}$, each fixed by the coefficientwise action `arithmeticGalois (modularFunctionFieldFull (1 * q)) σ` for all $\sigma\in S$, such that for each $i$ some nonzero $\overline{\mathbb Q}$-multiple of the expansion of $b_i$, and likewise of $w_q b_i$, has all coefficients in $A$. Then there exist $G_1,\dots,G_n\in V$, all lying in $R_1$ and in $R_2$, each fixed by `arithmeticGalois` at every $\sigma\in S$, such that the family of residue pairs $i\mapsto(\mathrm{res}_{R_1}G_i,\mathrm{res}_{R_2}G_i)$ is linearly independent over $\kappa_A$.
--
--   This is the Galois-equivariant form of the residue-pair independence statement for reduction of the function field of $X_0(q)$ along a prolongation of a valuation of $\overline{\mathbb Q}$ and its Fricke transport: an $S$-invariant basis with bounded denominators can be replaced by an $S$-invariant family in the same space whose pairs of residues at the two prolongations remain independent over the residue field. It is used in the construction of functions in a Riemann–Roch space with prescribed residues that are invariant under inertia, via [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (R₁ R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q))
      (modularFunctionFieldFullC (ResidueField A) 1))
    (h₁ : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
        ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (h₂ : ∀ f : modularFunctionFieldBar (1 * q),
      f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers)
    (h₂' : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
      R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (h₂ f).mp h⟩)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • b i = b i) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • G i = G i := by sorry
