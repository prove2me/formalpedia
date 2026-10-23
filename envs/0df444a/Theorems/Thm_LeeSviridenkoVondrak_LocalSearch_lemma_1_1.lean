-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_1_1
-- name    : LeeSviridenkoVondrak.LocalSearch.lemma_1_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:30.956752+00:00
-- url     : https://prove2.me/theorems/d4f4c53f-8d89-4e9c-b742-3ba32bc1f5bd
-- title:
--   Lemma 1.1 — Exact-cover addition inequality
-- statement:
--   Let $f$ be a submodular function on $N$. Let $S,C \subseteq N$ and let $\{T_l\}_{l=1}^t$ be a collection of subsets of $C\setminus S$ such that each element of $C\setminus S$ appears in exactly $k$ of these subsets. Then,
--   $$\sum_{l=1}^t (f(S\cup T_l)-f(S)) \ge k(f(S\cup C)-f(S)).$$ The paper’s standing nonnegativity convention applies to all objective values; no monotonicity or normalization is assumed.
--
--   This is a supporting statement for the monotone approximation guarantee.
--
--   **Formalization Note** The ground set is `Fin n`; all matroid ground sets equal the whole type. Indexed finite families preserve repetitions and allow empty index sets.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Lemma 1.1, printed p. 797, PDF p. 3

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

theorem lemma_1_1 {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : Nonnegative f)
    (S C : Finset (Fin n)) (t q : ℕ) (T : Fin t → Finset (Fin n))
    (hT : ∀ i, T i ⊆ C \ S) (hcover : ∀ x ∈ C \ S, multiplicity T x = q) :
    (q : ℝ) * (f (S ∪ C) - f S) ≤ ∑ i, (f (S ∪ T i) - f S) := by sorry

end LeeSviridenkoVondrak.LocalSearch
