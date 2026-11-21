-- Prove2me | Theorems.Thm_LocallyConvex_frechet_closedDisk_image_absorption
-- name    : LocallyConvex.frechet_closedDisk_image_absorption
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T00:33:16.62039+00:00
-- url     : https://prove2.me/theorems/58e572d7-cf12-4e2d-983d-e7228693b01c
-- title:
--   Bounded-set transport through a closed disk between Frechet presentations
-- statement:
--   Let $A$ and $B$ be complex Fréchet spaces, let $Q$ be a Hausdorff complex topological vector space, and let $a:A\to Q$ and $b:B\to Q$ be continuous complex-linear maps. Regard $Q$ also as a real vector space by restricting scalars. Suppose that $C\subseteq Q$ is closed and absolutely convex over $\mathbb R$, that $C\subseteq b(B)$, and that $S\subseteq A$ is bounded with $a(S)\subseteq C$.
--
--   Then every zero-neighborhood $W\subseteq B$ admits a real number $R>0$ such that
--
--   $$\forall r\in\mathbb R,\quad r\ge R\ \Longrightarrow\ \forall x\in S\ \exists w\in W,\quad a(x)=r\,b(w).$$
--
--   This is boundedness of the transported set in the quotient topology of $B/\ker b$. The map $b$ need not be injective, its range need not be closed in $Q$, and the assertion does not require a bounded set of representatives in $B$. Real absolute convexity is sufficient. The lemma isolates the finite-space Banach-disk transport step used in the localized-closure route to condition $(wQ)$ for strict LF quotients.
--
--   This is a derived auxiliary statement, not a quotation from the source. Its accepted formal proof constructs an $\ell^1$ extension of an arbitrary bounded family and factors it through $B/\ker b$. It is used by [null-sequence boundedness in a localized quotient stage](https://prove2.me/theorems/692d9333-b8dd-422a-9f51-b326af4e1cbe).
-- source:
--   Derived Banach-disk/closed-graph auxiliary lemma for LocallyConvex.strictLF_localized_nullSequence_bounded, https://prove2.me/theorems/692d9333-b8dd-422a-9f51-b326af4e1cbe . Banach-disk source: I. Monterde and V. Montesinos, Convex-compact sets and Banach discs, Czechoslovak Mathematical Journal 59 (2009), 773–780, introduction p. 773 and Theorem 3 p. 774, https://dml.cz/bitstream/handle/10338.dmlcz/140515/CzechMathJ_59-2009-3_16.pdf . This finite-space transport statement is a derived consequence, not a verbatim assertion of that paper; its derivation uses the Frechet closed-graph theorem after passing to B/ker(b). The verified summation and factorization helpers adapt Prove2Me contributor marozols, submission 07895212-fd3d-40f2-8193-6512eb6d0c60 (Apache 2.0), for https://prove2.me/theorems/692d9333-b8dd-422a-9f51-b326af4e1cbe .

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH Topology

theorem LocallyConvex.frechet_closedDisk_image_absorption
    (A : Type*) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    (B : Type*) [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (Q : Type*) [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q] [T2Space Q]
    (hA : IsFrechet A) (hB : IsFrechet B)
    (a : A →L[ℂ] Q) (b : B →L[ℂ] Q)
    (C : Set Q) (hCclosed : IsClosed C) (hCdisk : AbsConvex ℝ C)
    (hCimage : C ⊆ Set.range b)
    (S : Set A) (hS : Bornology.IsVonNBounded ℂ S) (hSC : a '' S ⊆ C) :
    ∀ W ∈ nhds (0 : B), ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∀ x ∈ S, ∃ w ∈ W, a x = (r : ℂ) • b w := by sorry
