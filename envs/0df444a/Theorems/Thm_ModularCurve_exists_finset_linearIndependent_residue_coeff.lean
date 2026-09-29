-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_linearIndependent_residue_coeff
-- name    : ModularCurve.exists_finset_linearIndependent_residue_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1c8bc475-9403-5a15-bdb0-048dd618bc99
-- title:
--   Coefficientwise reductions of independent modular functions at almost all primes
-- statement:
--   Fix $N \ge 1$ and $r \in \mathbb{N}$, and let $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` be a family of elements of the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the level-$N$ modular function field `modularFunctionFieldFull N` $= \mathbb{Q}(\text{divisorExpansions } N) \subseteq \mathbb{Q}((q))$, and assume the $s_i$ are linearly independent over $\overline{\mathbb{Q}}$. The assertion is that there exists a finite set $S \subseteq \mathbb{N}$, all of whose members are prime, with the following property: for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (the predicate `LiesOverPrime`), and every proof that all Laurent coefficients $a_k(s_i)$, for $i \in \mathrm{Fin}\,r$ and $k \in \mathbb{Z}$, lie in $A$, the $r$ functions $\mathbb{Z} \to \mathrm{ResidueField}\,A$ sending $k$ to the residue of $a_k(s_i)$ are linearly independent over the residue field of $A$, as elements of the module of all functions $\mathbb{Z} \to \mathrm{ResidueField}\,A$.
--
--   This is the statement that linear independence over $\overline{\mathbb{Q}}$ of $q$-expansions of modular functions of level $N$ survives coefficientwise reduction at every place of $\overline{\mathbb{Q}}$ lying over a prime outside a suitable finite exceptional set. It is used in the construction of reductions of chart data for the modular curve, in [`ModularCurve.exists_constantReduction_chartData_of_isEmbBasis`](thm.html#ModularCurve.exists_constantReduction_chartData_of_isEmbBasis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_linearIndependent_residue_coeff.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finset_linearIndependent_residue_coeff (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : LinearIndependent (AlgebraicClosure ℚ) s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ hint : ∀ (i : Fin r) (k : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) ∈ A,
          LinearIndependent (IsLocalRing.ResidueField A)
            (fun i : Fin r => fun k : ℤ => IsLocalRing.residue A ⟨_, hint i k⟩) := by sorry
