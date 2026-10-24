-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_2_7
-- name    : LeeSviridenkoVondrak.LocalSearch.lemma_2_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:28.388623+00:00
-- url     : https://prove2.me/theorems/775821fb-9fe2-4ba4-a0a5-f2a3992d7d4f
-- title:
--   Lemma 2.7 — Bounded-multiplicity exchange for independent sets
-- statement:
--   Let $\mathcal M = (N,\mathcal F)$ be a matroid and $I,J \in \mathcal F$. Let $I_1,\ldots,I_m$ be subsets of $I$ such that each element of $I$ appears in at most $q$ of them. Then, there are sets $J_1,\ldots,J_m \subseteq J$ such that each element of $J$ appears in at most $q$ of them and, for each $i$, $I_i \cup (J\setminus J_i) \in \mathcal F$.
--
--   This is a supporting statement for the monotone approximation guarantee.
--
--   **Formalization Note** The ground set is `Fin n`; all matroid ground sets equal the whole type. Indexed finite families preserve repetitions and allow empty index sets.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Lemma 2.7, printed p. 801, PDF p. 7

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

theorem lemma_2_7 {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (I J : Finset (Fin n)) (hI : M.Indep (↑I : Set (Fin n)))
    (hJ : M.Indep (↑J : Set (Fin n))) (m q : ℕ) (Is : Fin m → Finset (Fin n))
    (hIs : ∀ i, Is i ⊆ I) (hcover : ∀ x ∈ I, multiplicity Is x ≤ q) :
    ∃ Js : Fin m → Finset (Fin n), (∀ i, Js i ⊆ J) ∧
      (∀ x ∈ J, multiplicity Js x ≤ q) ∧
      ∀ i, M.Indep (↑(Is i ∪ (J \ Js i)) : Set (Fin n)) := by sorry

end LeeSviridenkoVondrak.LocalSearch
