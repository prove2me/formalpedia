-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_lemma_3_2
-- name    : LeeSviridenkoVondrak.LocalSearch.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:46.140831+00:00
-- url     : https://prove2.me/theorems/18027ff9-d7d4-46b0-bb65-21dac261df19
-- title:
--   Lemma 3.2 — Approximate local-search inequality
-- statement:
--   For an approximate locally optimal solution $S$ and any $C \in \bigcap_{j=1}^k \mathcal F_j$,
--   $$(1+\varepsilon)(k+1/p)\cdot f(S) \ge f(S\cup C)+(k-1+1/p)\cdot f(S\cap C),$$
--   where $\varepsilon > 0$ is the parameter used in the procedure of Figure 1. Here $p\ge1$ and $k\ge2$ are integers, $f$ is nonnegative on every subset and submodular, and all matroids have the same finite ground set. No monotonicity or normalization is assumed. Approximate local optimality is the literal no-move condition for Figure 1: every feasible $p$-neighbor has value strictly less than $(1+\varepsilon/[n(k+1)])f(S)$.
--
--   This is a supporting statement for the monotone approximation guarantee.
--
--   **Formalization Note** The ground set is `Fin n`; all matroid ground sets equal the whole type. Indexed finite families preserve repetitions and allow empty index sets.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Lemma 3.2, printed p. 803, PDF p. 9

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

theorem lemma_3_2 {n k p : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p)
    (f : Finset (Fin n) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : Nonnegative f) (M : Fin k → Matroid (Fin n))
    (hE : ∀ j, (M j).E = Set.univ) (S C : Finset (Fin n))
    (hC : CommonIndependent M C)
    (ε : ℝ) (hε : 0 < ε) (hS : ApproxLocalOptimum f M p ε S) :
    f (S ∪ C) + ((k : ℝ) - 1 + 1 / (p : ℝ)) * f (S ∩ C) ≤
      (1 + ε) * ((k : ℝ) + 1 / (p : ℝ)) * f S := by sorry

end LeeSviridenkoVondrak.LocalSearch
