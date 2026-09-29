-- Prove2me | Theorems.Thm_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional
-- name    : ModularCurve.exists_linearIndependent_residuePair_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/60fd6fc7-741c-55ef-99f1-222c3ed41325
-- title:
--   Residue-pair independent integral families in finite-dimensional subspaces
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$, with residue field $k$. Write $F$ for `modularFunctionFieldBar (1 * q)`, the subfield of $\overline{\mathbb Q}(\!(\,\cdot\,)\!)$ obtained from `modularFunctionFieldFull (1 * q)` by coefficientwise base change to $\overline{\mathbb Q}$, and let $R_1,R_2$ be two regular prolongations of $A$ to $F$ with residue field `modularFunctionFieldFullC k 1` (each consists of a valuation subring of $F$ whose contraction to $\overline{\mathbb Q}$ is $A$, together with a surjective residue homomorphism whose kernel is the maximal ideal, compatible with the residue map of $A$ and such that every nonzero element of $F$ has a nonzero residue after scaling by a suitable element of $\overline{\mathbb Q}$). Assume: (h₁) every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}(\!(\,\cdot\,)\!)$ lies in $F$ belongs to $R_1$'s ring of integers, with $R_1$-residue equal, as a Laurent series over $k$, to the coefficientwise reduction of $y$; (h₂) $f$ lies in $R_2$'s integers if and only if `frickeInvolutionBar (1 * q) f` lies in $R_1$'s; (h₂') the $R_2$-residue of $f$ equals the $R_1$-residue of `frickeInvolutionBar (1 * q) f`. Let $V\subseteq F$ be a finite-dimensional $\overline{\mathbb Q}$-subspace, of rank $n$, and suppose $V$ contains a linearly independent family $b_1,\dots,b_n$ such that for each $i$ both $b_i$ and its Fricke transform become, after multiplication by some nonzero scalar of $\overline{\mathbb Q}$, the coefficientwise image of a Laurent series with coefficients in $A$. Then there are $G_1,\dots,G_n\in V$, each integral for both $R_1$ and $R_2$, whose residue pairs $(\rho_1(G_i),\rho_2(G_i))$ in `modularFunctionFieldFullC k 1` $\times$ `modularFunctionFieldFullC k 1` are linearly independent over $k$.
--
--   This is the module-theoretic input of a Deuring-style reduction argument for the two Gauss norms of $X_0(q)$ at $q$: it produces, inside a finite-dimensional space of functions with $A$-integral expansions, as many elements as the dimension whose pairs of residues at the two prolongations remain independent over the (possibly non-discrete) residue field of $A$. It is used in the analysis of prolongation pairs over level one, in the lemmas producing elements of Riemann–Roch spaces with prescribed order or prescribed residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional.lean

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

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_linearIndependent_residuePair_of_finiteDimensional
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
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) := by sorry
