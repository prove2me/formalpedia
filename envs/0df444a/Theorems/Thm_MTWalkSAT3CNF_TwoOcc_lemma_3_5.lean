-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_lemma_3_5
-- name    : MTWalkSAT3CNF.TwoOcc.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:54.42569+00:00
-- url     : https://prove2.me/theorems/5f7bb50a-6797-46d5-a770-51a1d697e192
-- title:
--   Lemma 3.5 — every component outside $A$ is a defect tree, a boundary tree or unicyclic
-- statement:
--   Assume $\Delta(F)\le2$ and that every variable occurring twice has one positive and one negative occurrence. Fix any assignment, let $A=\{C:s(C)\ge2\}$, and consider the multigraph of clauses with $A$ deleted. Every connected component outside $A$ is **exactly one** of the following:
--
--   1. a tree with one unsatisfied clause and no true boundary occurrence;
--   2. a tree with no unsatisfied clause and one true boundary occurrence;
--   3. a unicyclic component with no unsatisfied clause and no true boundary occurrence.
--
--   This classification is what makes the global potential $\Phi$ of display (1) well defined: defect trees have a unique root (their unsatisfied clause) and boundary trees a unique root (the clause carrying the true boundary occurrence).
--
--   Differences from the source:
--   - encoding: a connected component outside A; tree; unicyclic → the component K(r) of a clause r ∉ A; e + 1 = q; e = q, with e the number of multigraph edges inside K; reason: every component is K(r) for each of its clauses; for a connected multigraph a tree is e = q − 1 and unicyclic is e = q
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Lemma 3.5, p. 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc

/-- Lemma 3.5, p. 13: in the opposite-sign case with `Δ(F) ≤ 2`, for every assignment, every
connected component `K` outside `A` is exactly one of: (1) a tree with one unsatisfied clause and
no true boundary occurrence; (2) a tree with no unsatisfied clause and one true boundary
occurrence; (3) a unicyclic component with no unsatisfied clause and no true boundary
occurrence. -/
theorem lemma_3_5 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (σ : V → Bool) (r : Fin m)
    (hr : ¬ InA F σ r) :
    let K := comp F σ r
    let P₁ := IsTreeComp F K ∧ unsatCount F σ K = 1 ∧ trueBoundaryCount F σ K = 0
    let P₂ := IsTreeComp F K ∧ unsatCount F σ K = 0 ∧ trueBoundaryCount F σ K = 1
    let P₃ := IsUnicyclicComp F K ∧ unsatCount F σ K = 0 ∧ trueBoundaryCount F σ K = 0
    (P₁ ∧ ¬ P₂ ∧ ¬ P₃) ∨ (¬ P₁ ∧ P₂ ∧ ¬ P₃) ∨ (¬ P₁ ∧ ¬ P₂ ∧ P₃) := by sorry

end MTWalkSAT3CNF.TwoOcc
