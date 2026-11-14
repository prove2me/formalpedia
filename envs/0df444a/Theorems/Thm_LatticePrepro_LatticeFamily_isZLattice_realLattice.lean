-- Prove2me | Theorems.Thm_LatticePrepro_LatticeFamily_isZLattice_realLattice
-- name    : LatticePrepro.LatticeFamily.isZLattice_realLattice
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:49.287916+00:00
-- url     : https://prove2.me/theorems/7eb74bdd-de4b-46d1-b1dd-1da7d06f3294
-- title:
--   Full rank in Mathlib terms — a lattice containing $N\cdot\mathbb Z^M$ is a Mathlib IsZLattice (Section 3, Lemma 3.12)
-- statement:
--   Let $(\Lambda,(t_x)_{x\in X})$ be a lattice family, with $\Lambda\subseteq\mathbb Z^M$ an additive subgroup, and let $N$ be a natural number with $N>0$ such that
--   $$N\cdot v\in\Lambda\qquad\text{for every }v\in\mathbb Z^M,$$
--   i.e. $N\cdot\mathbb Z^M\subseteq\Lambda$. Then the real image $\Lambda_{\mathbb R}\subseteq\mathbb R^M$ of $\Lambda$ is a full-rank lattice in Mathlib's sense, `IsZLattice ℝ Λ.realLattice`: a discrete $\mathbb Z$-submodule of $\mathbb R^M$ whose $\mathbb R$-linear span is all of $\mathbb R^M$.
--
--   Section 3 defines a lattice as a discrete additive subgroup of $\mathbb R^M$ and assumes full rank throughout; Lemma 3.12 and Theorem 5.1 produce full-rank lattices $\Lambda\subseteq\mathbb Z^M$. The formalization records full rank as the condition $N\cdot\mathbb Z^M\subseteq\Lambda$ (a field of `LatticeReduction` and of the final `LatticeGap`), and this theorem shows that the condition yields Mathlib's notion. It is used to show that the lattices of Theorem 5.1 are `IsZLattice`s.
--
--   **Formalization Note.** Mathlib's class `IsZLattice ℝ L` takes the discreteness of $L$ as a `DiscreteTopology` instance argument (provided for every lattice family by the instance `discreteTopology_realLattice`) and has the single field `span_top : span ℝ L = ⊤`. Here $\mathbb R^M$ is the function space `M → ℝ`, and $\Lambda_{\mathbb R}$ is `LatticeFamily.realLattice`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Section 3 (Preliminaries, \label{sec:preliminaries}), definition of full-rank lattices, and the full-rank condition of Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Lattices/Mathlib.lean, LatticePrepro.LatticeFamily.isZLattice_realLattice

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

theorem LatticePrepro.LatticeFamily.isZLattice_realLattice {N : ℕ} (hN : 0 < N)
    (h : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice) : IsZLattice ℝ Λ.realLattice := by sorry
