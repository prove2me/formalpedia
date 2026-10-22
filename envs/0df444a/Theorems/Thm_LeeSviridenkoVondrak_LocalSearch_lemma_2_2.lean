-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_2_2
-- name    : LeeSviridenkoVondrak.LocalSearch.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:22.885768+00:00
-- url     : https://prove2.me/theorems/5a444f2b-c8a4-4a13-96d3-937c5fde72e8
-- title:
--   Lemma 2.2 — Unique perfect matching implies independence
-- statement:
--   Let $|I| = |J|$ and $I \in \mathcal F_l$ for $l = 1,2$, and assume that $D_{\mathcal M_l}(I)$ has a unique perfect matching between $I\setminus J$ and $J\setminus I$. Then, $J \in \mathcal F_l$.
--
--   This is a supporting statement for the monotone approximation guarantee.
--
--   **Formalization Note** The ground set is `Fin n`; all matroid ground sets equal the whole type. Indexed finite families preserve repetitions and allow empty index sets.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Lemma 2.2, printed p. 798, PDF p. 4

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Exchange
open scoped symmDiff

/- Imported definition bodies, reproduced verbatim as code context for auditing.
namespace NonmonotoneSubmod.Shared


def Submodular {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ S T : Finset X, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

end NonmonotoneSubmod.Shared

namespace LeeSviridenkoVondrak.LocalSearch


def Nonnegative {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop := ∀ A, 0 ≤ f A

def Nondecreasing {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ A B, A ⊆ B → f A ≤ f B

def CommonIndependent {n k : ℕ} (M : Fin k → Matroid (Fin n))
    (S : Finset (Fin n)) : Prop := ∀ j, (M j).Indep (↑S : Set (Fin n))


noncomputable def optimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) : ℝ :=
  sSup {v | ∃ S : Finset (Fin n), CommonIndependent M S ∧ v = f S}

def PNeighbor {n k : ℕ} (M : Fin k → Matroid (Fin n)) (p : ℕ)
    (S T : Finset (Fin n)) : Prop :=
  CommonIndependent M T ∧ (T \ S).card ≤ 2 * p ∧ (S \ T).card ≤ 2 * k * p

def ExactLocalOptimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) (p : ℕ) (S : Finset (Fin n)) : Prop :=
  CommonIndependent M S ∧ ∀ T, PNeighbor M p S T → f T ≤ f S


def ApproxLocalOptimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) (p : ℕ) (ε : ℝ) (S : Finset (Fin n)) : Prop :=
  CommonIndependent M S ∧ ∀ T, PNeighbor M p S T →
    f T < (1 + ε / ((n : ℝ) * ((k : ℝ) + 1))) * f S


def multiplicity {n m : ℕ} (A : Fin m → Finset (Fin n)) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => x ∈ A i)).card

end LeeSviridenkoVondrak.LocalSearch

open scoped symmDiff

namespace LeeSviridenkoVondrak.LocalSearch


def ExchangeArc {n : ℕ} (M : Matroid (Fin n)) (I : Finset (Fin n))
    (x y : Fin n) : Prop :=
  x ∈ I ∧ y ∉ I ∧ M.Indep (↑(insert y (I.erase x)) : Set (Fin n))

def TwoArc {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (x y : Fin n) : Prop := ExchangeArc M₁ I x y ∨ ExchangeArc M₂ I y x


def PerfectMatching {n : ℕ} (M : Matroid (Fin n)) (I L R : Finset (Fin n))
    (E : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ E, e.1 ∈ L ∧ e.2 ∈ R ∧ ExchangeArc M I e.1 e.2) ∧
  (∀ x ∈ L, ∃! y, (x, y) ∈ E) ∧ (∀ y ∈ R, ∃! x, (x, y) ∈ E)


structure WalkData (n : ℕ) where
  vertices : List (Fin n)
  closed : Bool

def WalkData.support {n : ℕ} (A : WalkData n) : Finset (Fin n) := A.vertices.toFinset

def WalkData.edge {n : ℕ} (A : WalkData n) (x y : Fin n) : Prop :=
  (x, y) ∈ A.vertices.zip A.vertices.tail ∨
    (A.closed = true ∧ A.vertices.getLast? = some x ∧ A.vertices.head? = some y)

def WalkData.endpoint {n : ℕ} (A : WalkData n) (x : Fin n) : Prop :=
  A.closed = false ∧ (A.vertices.head? = some x ∨ A.vertices.getLast? = some x)

def IsDirected {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  A.vertices ≠ [] ∧ A.vertices.Nodup ∧ (A.closed = true → 2 ≤ A.vertices.length) ∧
    ∀ x y, A.edge x y → TwoArc M₁ M₂ I x y


def IsSubpath {n : ℕ} (A B : WalkData n) : Prop :=
  B.closed = false ∧ B.vertices ≠ [] ∧ B.vertices.Nodup ∧
    B.support ⊆ A.support ∧ ∀ x y, B.edge x y → A.edge x y


def Irreducible {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  IsDirected M₁ M₂ I A ∧ A.closed = true ∧
    (∃! E, PerfectMatching M₁ I (I ∩ A.support) (A.support \ I) E) ∧
    (∃! E, PerfectMatching M₂ I (I ∩ A.support) (A.support \ I) E)


def FeasibleWalk {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  IsDirected M₁ M₂ I A ∧
  (M₁.Indep (↑(I ∆ A.support) : Set (Fin n)) ∧
   M₂.Indep (↑(I ∆ A.support) : Set (Fin n))) ∧
  ∀ B, IsSubpath A B → (∀ x, B.endpoint x → A.endpoint x ∨ x ∈ I) →
    M₁.Indep (↑(I ∆ B.support) : Set (Fin n)) ∧
    M₂.Indep (↑(I ∆ B.support) : Set (Fin n))

end LeeSviridenkoVondrak.LocalSearch
-/

namespace LeeSviridenkoVondrak.LocalSearch

theorem lemma_2_2 {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (I J : Finset (Fin n)) (hI : M.Indep (↑I : Set (Fin n)))
    (hcard : I.card = J.card)
    (hunique : ∃! E, PerfectMatching M I (I \ J) (J \ I) E) :
    M.Indep (↑J : Set (Fin n)) := by sorry

end LeeSviridenkoVondrak.LocalSearch
