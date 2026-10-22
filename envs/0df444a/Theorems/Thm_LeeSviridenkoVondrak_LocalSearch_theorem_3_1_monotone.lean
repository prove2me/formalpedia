-- Prove2me | Theorems.Thm_LeeSviridenkoVondrak_LocalSearch_theorem_3_1_monotone
-- name    : LeeSviridenkoVondrak.LocalSearch.theorem_3_1_monotone
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:30.341789+00:00
-- url     : https://prove2.me/theorems/51d8e272-cbde-4ca0-b7e5-efeda39e0dfd
-- title:
--   Theorem 3.1 — Polynomial approximation for monotone submodular maximization
-- statement:
--   For each fixed integer $k\ge2$ and real constant $\delta>0$, there is a polynomial-time oracle algorithm for maximizing any nonnegative, nondecreasing submodular function under $k$ matroid constraints. On every finite ground set of size $n$, the algorithm returns a common independent set $S$ satisfying
--   $$f(S)\ge\frac{\mathrm{OPT}}{k+\delta}.$$
--   The algorithm accesses the objective only by value queries and the matroids only by independence queries. There exist one finite program and polynomial constants depending only on $k,\delta$, valid for every $n$, every objective and every family of input matroids. The program halts with its entire execution cost bounded by $A(n+1)^d$, including initialization, successful and unsuccessful searches, set processing, and output. Empty ground sets, loops, zero objectives and nonzero $f(\varnothing)$ are included.
--
--   This is the first sentence of Theorem 3.1, retaining its approximation factor and polynomial algorithmic conclusion. The separate linear-objective guarantee is outside this mission.
--
--   **Formalization Note** Finite real-RAM instructions make oracle access and cost operational, with unit-cost real arithmetic and comparisons and conservative $n+1$ padding per instruction for subset processing. This is oracle complexity, not bit complexity. The existential algorithm may complete Figure 1 by filtering infeasible singletons and handling empty and zero-value branches; these are implementation choices, not added input assumptions. No local optimality or stopping bound is a premise.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; Theorem 3.1, first sentence, printed p. 803 / PDF 9; oracle model p. 795 / PDF 1

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_OracleMachine
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

namespace LeeSviridenkoVondrak.LocalSearch


inductive Instruction where
  | natConst (dst value : ℕ)
  | natCopy (dst src : ℕ)
  | natAdd (dst a b : ℕ)
  | natSub (dst a b : ℕ)
  | natBranch (a b yes no : ℕ)
  | realConst (dst : ℕ) (value : ℝ)
  | realCopy (dst src : ℕ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  | realDiv (dst a b : ℕ)
  | realBranch (a b yes no : ℕ)
  | setEmpty (dst : ℕ)
  | setCopy (dst src : ℕ)
  | setInsert (dst src elementRegister : ℕ)
  | setErase (dst src elementRegister : ℕ)
  | setMember (setRegister elementRegister yes no : ℕ)
  | valueQuery (realDst setRegister : ℕ)
  | indepQuery (natDst matroidRegister setRegister : ℕ)
  | jump (label : ℕ)
  | halt (setRegister : ℕ)

structure MachineState (n : ℕ) where
  pc : ℕ
  natReg : ℕ → ℕ
  realReg : ℕ → ℝ
  setReg : ℕ → Finset (Fin n)
  halted : Bool
  output : Finset (Fin n)
  cost : ℕ

def initialState (n : ℕ) : MachineState n :=
  ⟨0, (fun r => if r = 0 then n else 0), (fun _ => 0), (fun _ => ∅), false, ∅, 0⟩


noncomputable def machineStep {n k : ℕ} (code : List Instruction)
    (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))
    (s : MachineState n) : MachineState n := by
  classical
  exact if s.halted then s else
    match code[s.pc]? with
    | none => { s with cost := s.cost + n + 1 }
    | some op =>
      let t := { s with pc := s.pc + 1, cost := s.cost + n + 1 }
      match op with
      | .natConst d v => { t with natReg := Function.update s.natReg d v }
      | .natCopy d a => { t with natReg := Function.update s.natReg d (s.natReg a) }
      | .natAdd d a b => { t with natReg := Function.update s.natReg d (s.natReg a + s.natReg b) }
      | .natSub d a b => { t with natReg := Function.update s.natReg d (s.natReg a - s.natReg b) }
      | .natBranch a b y z => { t with pc := if s.natReg a ≤ s.natReg b then y else z }
      | .realConst d v => { t with realReg := Function.update s.realReg d v }
      | .realCopy d a => { t with realReg := Function.update s.realReg d (s.realReg a) }
      | .realAdd d a b => { t with realReg := Function.update s.realReg d (s.realReg a + s.realReg b) }
      | .realSub d a b => { t with realReg := Function.update s.realReg d (s.realReg a - s.realReg b) }
      | .realMul d a b => { t with realReg := Function.update s.realReg d (s.realReg a * s.realReg b) }
      | .realDiv d a b => { t with realReg := Function.update s.realReg d (s.realReg a / s.realReg b) }
      | .realBranch a b y z => { t with pc := if s.realReg a ≤ s.realReg b then y else z }
      | .setEmpty d => { t with setReg := Function.update s.setReg d ∅ }
      | .setCopy d a => { t with setReg := Function.update s.setReg d (s.setReg a) }
      | .setInsert d a e =>
        { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then insert ⟨s.natReg e, h⟩ (s.setReg a) else s.setReg a)) }
      | .setErase d a e =>
        { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then (s.setReg a).erase ⟨s.natReg e, h⟩ else s.setReg a)) }
      | .setMember a e y z =>
        { t with pc := if h : s.natReg e < n then
            (if (⟨s.natReg e, h⟩ : Fin n) ∈ s.setReg a then y else z) else z }
      | .valueQuery d a => { t with realReg := Function.update s.realReg d (f (s.setReg a)) }
      | .indepQuery d j a =>
        { t with natReg := (Function.update s.natReg d (if h : s.natReg j < k then
            (if (M ⟨s.natReg j, h⟩).Indep (↑(s.setReg a) : Set (Fin n)) then 1 else 0)
           else 0)) }
      | .jump j => { t with pc := j }
      | .halt a => { t with halted := true, output := s.setReg a }


noncomputable def runMachine {n k : ℕ} (code : List Instruction)
    (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n)) (steps : ℕ) : MachineState n :=
  (machineStep code f M)^[steps] (initialState n)

end LeeSviridenkoVondrak.LocalSearch
-/

namespace LeeSviridenkoVondrak.LocalSearch

theorem theorem_3_1_monotone (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ code : List Instruction, ∃ A d : ℕ, 0 < A ∧
      ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n)),
        (∀ j, (M j).E = Set.univ) → Nonnegative f → Nondecreasing f →
        NonmonotoneSubmod.Shared.Submodular f →
        ∃ steps : ℕ,
          (runMachine code f M steps).halted = true ∧
          (runMachine code f M steps).cost ≤ A * (n + 1) ^ d ∧
          CommonIndependent M (runMachine code f M steps).output ∧
          optimum f M / ((k : ℝ) + δ) ≤ f (runMachine code f M steps).output := by sorry

end LeeSviridenkoVondrak.LocalSearch
