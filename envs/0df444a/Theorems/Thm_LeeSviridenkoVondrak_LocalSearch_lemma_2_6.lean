-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_2_6
-- name    : LeeSviridenkoVondrak.LocalSearch.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:35.981911+00:00
-- url     : https://prove2.me/theorems/9ace34de-f604-409e-ba88-e6933d3f27cc
-- title:
--   Lemma 2.6 — Generalized Rota exchange
-- statement:
--   Let $\mathcal M = (N,\mathcal F)$ be a matroid and $A,B$ bases in $\mathcal M$. Let $A_1,\ldots,A_m$ be subsets of $A$ such that each element of $A$ appears in exactly $q$ of them. Then, there are sets $B_1,\ldots,B_m \subseteq B$ such that each element of $B$ appears in exactly $q$ of them and, for each $i$, $A_i \cup (B\setminus B_i) \in \mathcal F$.
--
--   This is a supporting statement for the monotone approximation guarantee.
--
--   **Formalization Note** The ground set is `Fin n`; all matroid ground sets equal the whole type. Indexed finite families preserve repetitions and allow empty index sets.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Lemma 2.6, printed p. 800, PDF p. 6

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
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
-/

namespace LeeSviridenkoVondrak.LocalSearch

theorem lemma_2_6 {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (A B : Finset (Fin n)) (hA : M.IsBase (↑A : Set (Fin n)))
    (hB : M.IsBase (↑B : Set (Fin n))) (m q : ℕ) (As : Fin m → Finset (Fin n))
    (hAs : ∀ i, As i ⊆ A) (hcover : ∀ x ∈ A, multiplicity As x = q) :
    ∃ Bs : Fin m → Finset (Fin n), (∀ i, Bs i ⊆ B) ∧
      (∀ x ∈ B, multiplicity Bs x = q) ∧
      ∀ i, M.Indep (↑(As i ∪ (B \ Bs i)) : Set (Fin n)) := by sorry

end LeeSviridenkoVondrak.LocalSearch
