-- Prove2me | Theorems.Thm_OneEdgeRawLocalFiniteCover
-- name    : OneEdgeRawLocalFiniteCover
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:41:13.205861+00:00
-- url     : https://prove2.me/theorems/2eea4ac1-038e-41e2-8348-2cebfbce17fa
-- title:
--   One Edge Raw Local Finite Cover
-- statement:
--   Let $A\subseteq\mathbb R^2$, let $C_\sigma$ be a complement component of
--   $A$, and let $a,b\in\mathbb R^2$ with endpoint radii $r_a,r_b$.  Suppose
--   we are given finite endpoint-sector families
--   $\{S^a_i\}_{i\in I_a}$ and $\{S^b_j\}_{j\in I_b}$, a middle rectangle
--   $R$, and two middle side pieces $L$ and $M$.  Assume that each endpoint
--   sector is open, connected, and contained in the corresponding endpoint ball
--   and in the complement of $A\cup[a,b]$ (for the $b$-sectors, written with
--   the opposite orientation $[b,a]$); that $L$ and $M$ are connected subsets of
--   $(A\cup[a,b])^c$; that
--   $$
--     R\setminus[a,b]\subseteq L\cup M;
--   $$
--   that the $a$-sectors cover
--   $B(a,r_a)\cap(A\cup[a,b])^c$ and the $b$-sectors cover
--   $B(b,r_b)\cap(A\cup[b,a])^c$; and that each middle side piece meets at
--   least one $a$-sector and at least one $b$-sector.
--
--   Then there is a finite indexed raw local family $Q_k$, whose members are
--   exactly the endpoint sectors and the two middle side pieces that meet
--   $C_\sigma$, with the following properties.  An index is retained precisely
--   when $C_\sigma\cap Q_k\ne\varnothing$.  Every retained $Q_k$ is nonempty,
--   connected, contained in $(A\cup[a,b])^c$, and contained in $C_\sigma$.
--   Moreover every point of
--   $$
--     (B(a,r_a)\cup R\cup B(b,r_b))\cap C_\sigma
--   $$
--   that is not on $[a,b]$ lies in some retained $Q_k$.  Finally, if either
--   middle side piece is retained, then it meets a retained $a$-sector and a
--   retained $b$-sector.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeRawLocalFiniteCover`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeRawLocalFiniteCover.lean#L1-L218

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma OneEdgeRawLocalFiniteCover
    (A Csigma : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2)) (ra rb : ℝ)
    {ιA ιB : Type} [Fintype ιA] [Fintype ιB]
    (sectorA : ιA → Set (EuclideanSpace ℝ (Fin 2)))
    (sectorB : ιB → Set (EuclideanSpace ℝ (Fin 2)))
    (middleRect middleLeft middleRight : Set (EuclideanSpace ℝ (Fin 2)))
    (hCsigma : ComplementComponent A Csigma)
    (hsectorA_data :
      ∀ i, IsOpen (sectorA i) ∧ IsConnected (sectorA i) ∧
        sectorA i ⊆ Metric.ball a ra ∧
        sectorA i ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hsectorB_data :
      ∀ i, IsOpen (sectorB i) ∧ IsConnected (sectorB i) ∧
        sectorB i ⊆ Metric.ball b rb ∧
        sectorB i ⊆ (A ∪ segment ℝ b a)ᶜ)
    (hmiddleLeft_connected : IsConnected middleLeft)
    (hmiddleRight_connected : IsConnected middleRight)
    (hmiddleLeft_subset_compl : middleLeft ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hmiddleRight_subset_compl : middleRight ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hmiddle_cover : middleRect \ segment ℝ a b ⊆ middleLeft ∪ middleRight)
    (hsectorA_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball a ra → x ∈ (A ∪ segment ℝ a b)ᶜ →
          ∃ i, x ∈ sectorA i)
    (hsectorB_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball b rb → x ∈ (A ∪ segment ℝ b a)ᶜ →
          ∃ i, x ∈ sectorB i)
    (hmiddleLeft_sectorA : ∃ i, (middleLeft ∩ sectorA i).Nonempty)
    (hmiddleRight_sectorA : ∃ i, (middleRight ∩ sectorA i).Nonempty)
    (hmiddleLeft_sectorB : ∃ i, (middleLeft ∩ sectorB i).Nonempty)
    (hmiddleRight_sectorB : ∃ i, (middleRight ∩ sectorB i).Nonempty) :
    ∃ rawPieces : Finset ((ιA ⊕ ιB) ⊕ Bool),
      ∃ piece : ((ιA ⊕ ιB) ⊕ Bool) → Set (EuclideanSpace ℝ (Fin 2)),
        (∀ i, piece (Sum.inl (Sum.inl i)) = sectorA i) ∧
          (∀ i, piece (Sum.inl (Sum.inr i)) = sectorB i) ∧
          piece (Sum.inr false) = middleLeft ∧
          piece (Sum.inr true) = middleRight ∧
          (∀ k, k ∈ rawPieces ↔ (Csigma ∩ piece k).Nonempty) ∧
          (∀ k ∈ rawPieces,
            (piece k).Nonempty ∧ IsConnected (piece k) ∧
              piece k ⊆ (A ∪ segment ℝ a b)ᶜ ∧ piece k ⊆ Csigma) ∧
          (∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) ∩
                Csigma →
              x ∉ segment ℝ a b →
              ∃ k ∈ rawPieces, x ∈ piece k) ∧
          (((Sum.inr false : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
              ((∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleLeft ∩ sectorA i).Nonempty) ∧
                (∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleLeft ∩ sectorB i).Nonempty))) ∧
            ((Sum.inr true : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
              ((∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleRight ∩ sectorA i).Nonempty) ∧
                (∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleRight ∩ sectorB i).Nonempty)))) := by sorry
