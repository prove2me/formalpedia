-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_Supplement_lemma_6_7
-- name    : GreedyRegionGrowing.Layouts.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:22.273363+00:00
-- url     : https://prove2.me/theorems/27996170-1e2e-42a9-aa74-8b389cb61fec
-- title:
--   Lemma 6.7 — Directed radius and polynomial time
-- statement:
--   Under the Section 6.2 assumptions, every finite operational prefix of Algorithm 3 has at most n frames, has every post-step radius at least n/40, and every piece has at most 3n/4 vertices. Every such prefix extends to a complete run. Moreover, one deterministic polynomial-time machine, on the coded graph, optimal rational solution and admissible signs, outputs a complete operational run. Termination and the bounds are conclusions, not conditions on the run.
--
--   $$
--   \rho_{i+1}\ge n/40,\qquad k\le n,\qquad|X_i|\le3n/4.
--   $$
--
--   This is a supporting result for Theorem 6.1.
--
--   Differences from the source:
--   - encoding: finite labelled graphs, ordered iterations and polynomial-time algorithms → Fin n carriers, zero-based trace indices, fixed binary codes and deterministic TM2 polynomial time; reason: labels and iteration shifts change no source instance; the codes include all vertices and rational data, and the machine condition records the full runtime claim
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. Lemma 6.7, p. 32 (PDF p. 32).

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- Finite simple directed graphs (§3): a relation, with acyclicity imposed separately. -/
private abbrev ArcGraph (n : ℕ) := Fin n → Fin n → Prop

private def Acyclic {n : ℕ} (G : ArcGraph n) : Prop :=
  (∀ v, ¬ G v v) ∧ ∀ v, ¬ Relation.TransGen G v v

private def arcs {n : ℕ} (G : ArcGraph n) (U : Finset (Fin n)) :=
  (U ×ˢ U).filter (fun e => G e.1 e.2)

private def arcCut {n : ℕ} (G : ArcGraph n) (U S : Finset (Fin n)) :=
  (arcs G U).filter (fun e => (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ e.1 ∉ S))

private def Topological {n : ℕ} (G : ArcGraph n) (U : Finset (Fin n)) (p : List (Fin n)) : Prop :=
  IsOrdering U p ∧ ∀ e ∈ arcs G U, p.idxOf e.1 < p.idxOf e.2

private def storage {n : ℕ} (G : ArcGraph n) (p : List (Fin n)) : ℕ :=
  (range (p.length + 1)).sup (fun i => (arcCut G univ (orderingPrefix p i)).card)

private def registers {n : ℕ} (G : ArcGraph n) (p : List (Fin n)) : ℕ :=
  (range (p.length + 1)).sup (fun i =>
    ((orderingPrefix p i).filter (fun u => ∃ v, G u v ∧ v ∉ orderingPrefix p i)).card)

private def MS {n : ℕ} (G : ArcGraph n) : ℕ :=
  sInf {k | ∃ p, Topological G univ p ∧ storage G p = k}

private def MRS {n : ℕ} (G : ArcGraph n) : ℕ :=
  sInf {k | ∃ p, Topological G univ p ∧ registers G p = k}

private def weightedStorage {n : ℕ} (G : ArcGraph n) (w : Fin n → Fin n → ℚ)
    (p : List (Fin n)) : ℚ :=
  ((List.range (p.length + 1)).map (fun i =>
    ∑ e ∈ arcCut G univ (orderingPrefix p i), w e.1 e.2)).foldl max 0

private def WMS {n : ℕ} (G : ArcGraph n) (w : Fin n → Fin n → ℚ) : ℝ :=
  sInf {r | ∃ p, Topological G univ p ∧ r = (weightedStorage G w p : ℝ)}

private def dagCode {n : ℕ} (G : ArcGraph n) : Str :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => decide (G u v)))

private def matrixCode {n : ℕ} (d : Fin n → Fin n → ℚ) : Str :=
  (List.finRange n).flatMap (fun u => (List.finRange n).flatMap (fun v => ratCode (d u v)))

private def weightedDagCode {n : ℕ} (G : ArcGraph n) (w : Fin n → Fin n → ℚ) : Str :=
  dagCode G ++ (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => decide (G u v))).flatMap (fun v => ratCode (w u v)))

/-- All constraints of (6.1), including the signed empty-set right side. -/
private def DirectedFeasible {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧
  (∀ x y z, d x z ≤ d x y + d y z) ∧
  (∀ x y, G x y → d y x = 0) ∧
  ∀ u (S : Finset (Fin n)), ((S.card : ℚ)^2 - 1)/4 ≤ ∑ v ∈ S, (d u v + d v u)

private def directedObjective {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ) : ℚ :=
  ∑ e ∈ arcs G univ, d e.1 e.2

private def DirectedOptimal {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ) : Prop :=
  DirectedFeasible G d ∧ ∀ d', DirectedFeasible G d' →
    directedObjective G d ≤ directedObjective G d'

private def DLP {n : ℕ} (G : ArcGraph n) : ℝ :=
  sInf {r | ∃ d, DirectedFeasible G d ∧ r = (directedObjective G d : ℝ)}

private def WeakConnected {n : ℕ} (G : ArcGraph n) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun x y => G x y ∨ G y x) u v

private def orientedDistance {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool)
    (u v : Fin n) : ℚ := if s u then d u v else d v u

private def orientedBall {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool)
    (U : Finset (Fin n)) (u : Fin n) (r : ℝ) :=
  if r ≤ 0 then ∅ else U.filter (fun v => (orientedDistance d s u v : ℝ) < r)

private def SmallSigns {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool) : Prop :=
  ∀ u, ((orientedBall d s univ u ((n : ℝ)/20)).card : ℝ) ≤ 3*(n : ℝ)/4

private def directedSetVolume {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (S : Finset (Fin n)) : ℚ :=
  directedObjective G d * S.card / n + ∑ e ∈ arcs G S, d e.1 e.2

private def directedVolume {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
  let B := orientedBall d s U u r
  (directedSetVolume G d B : ℝ) +
    ∑ e ∈ (arcs G U).filter (fun e => if s u then e.1 ∈ B ∧ e.2 ∉ B
      else e.1 ∉ B ∧ e.2 ∈ B),
      (if s u then r - (d u e.1 : ℝ) else r - (d e.2 u : ℝ))

private def directedVolumeQ {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) (U : Finset (Fin n)) (u : Fin n) (r : ℚ) : ℚ :=
  if r ≤ 0 then 0 else
  let B := orientedBall d s U u (r : ℝ)
  directedSetVolume G d B +
    ∑ e ∈ (arcs G U).filter (fun e => if s u then e.1 ∈ B ∧ e.2 ∉ B
      else e.1 ∉ B ∧ e.2 ∈ B),
      (if s u then r - d u e.1 else r - d e.2 u)

private def directedEvents {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool)
    (U : Finset (Fin n)) (u : Fin n) : Finset ℚ := U.image (orientedDistance d s u)

/-- Algorithm 3, operational frame. No performance property is a field. -/
private structure DirectedFrame (n : ℕ) where
  U : Finset (Fin n)
  rho : ℚ
  center : Fin n
  radius : ℚ

namespace DirectedFrame
variable {n : ℕ}
private def K (f : DirectedFrame n) (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) : ℚ :=
  ((f.U.sort (· ≤ ·)).map (fun u => directedVolumeQ G d s f.U u f.rho)).foldl max 0

private def w (f : DirectedFrame n) (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) : ℚ := n * f.K G d s / (320 * directedObjective G d)

private def X (f : DirectedFrame n) (d : Fin n → Fin n → ℚ) (s : Fin n → Bool) :=
  orientedBall d s f.U f.center (f.radius : ℝ)

private def W (f : DirectedFrame n) (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) := directedVolume G d s f.U f.center (f.radius : ℝ)

private def nextU (f : DirectedFrame n) (d : Fin n → Fin n → ℚ) (s : Fin n → Bool) :=
  f.U \ f.X d s

private def Operational (f : DirectedFrame n) (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) : Prop :=
  f.center ∈ f.U ∧
  (let a := f.rho - f.w G d s
   let E := directedEvents d s f.U f.center
   (∀ u ∈ f.U, directedVolumeQ G d s f.U u a ≤ directedVolumeQ G d s f.U f.center a) ∧
   a < f.radius ∧ f.radius < f.rho ∧ f.radius ∉ E ∧
   ∀ r : ℚ, a < r → r < f.rho → r ∉ E →
     (arcCut G f.U (f.X d s)).card ≤
       (arcCut G f.U (orientedBall d s f.U f.center (r : ℝ))).card)
end DirectedFrame

private def DirectedRunFrom {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) : Finset (Fin n) → ℚ → List (DirectedFrame n) → Prop
  | _, _, [] => True
  | U, rho, f::fs => f.U = U ∧ f.rho = rho ∧ f.Operational G d s ∧
      DirectedRunFrom G d s (f.nextU d s) (rho-f.w G d s) fs

private def DirectedRun {n : ℕ} (G : ArcGraph n) (d : Fin n → Fin n → ℚ)
    (s : Fin n → Bool) (fs : List (DirectedFrame n)) := DirectedRunFrom G d s univ (n/20) fs

private def DirectedComplete {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool)
    (fs : List (DirectedFrame n)) : Prop :=
  match fs.getLast? with
  | none => n = 0
  | some f => f.nextU d s = ∅

private def directedFrameCode {n : ℕ} (f : DirectedFrame n) : Str :=
  setCode f.U ++ ratCode f.rho ++ natCode f.center.val ++ ratCode f.radius

private structure DirectedInput where
  n : ℕ
  G : ArcGraph n
  d : Fin n → Fin n → ℚ
  s : Fin n → Bool
  dag : Acyclic G
  connected : WeakConnected G
  size : 2 ≤ n
  optimal : DirectedOptimal G d
  signs : SmallSigns d s

private def directedInputCode (I : DirectedInput) : Str :=
  dagCode I.G ++ matrixCode I.d ++ (List.finRange I.n).map I.s

private def DirectedCarvingPolyTime : Prop :=
  ∃ F : (I : DirectedInput) → List (DirectedFrame I.n),
    PPSLattice.PolyTimeOn directedInputCode (fun I => listCode directedFrameCode (F I)) ∧
    ∀ I, DirectedRun I.G I.d I.s (F I) ∧ DirectedComplete I.d I.s (F I)

private def twoEnded {n : ℕ} (s : Fin n → Bool) (fs : List (DirectedFrame n)) : List (DirectedFrame n) :=
  fs.filter (fun f => s f.center) ++ (fs.filter (fun f => !(s f.center))).reverse

/-- Any ordering by contiguous blocks in the required order. -/
private def BlockOrdering {n : ℕ} (d : Fin n → Fin n → ℚ) (s : Fin n → Bool)
    (fs : List (DirectedFrame n)) (p : List (Fin n)) : Prop :=
  IsOrdering univ p ∧ ∃ blocks : List (List (Fin n)),
    blocks.length = fs.length ∧ blocks.flatten = p ∧
    ∀ i : Fin fs.length, IsOrdering ((fs.get i).X d s) (blocks[i.val]!)

/-- The concrete gadget of Appendix B; minus copies have tag false, plus copies true. -/
private def gadget {n : ℕ} (G : ArcGraph n) : ArcGraph (2*n) := fun x y =>
  (∃ v : Fin n, x.val = v.val ∧ y.val = n+v.val) ∨
  (∃ u v : Fin n, G u v ∧ x.val = u.val ∧ y.val = v.val) ∨
  (∃ u v : Fin n, G u v ∧ x.val = v.val ∧ y.val = n+u.val)

private def gadgetWeight {n : ℕ} (G : ArcGraph n) (x y : Fin (2*n)) : ℚ :=
  if ∃ v : Fin n, x.val = v.val ∧ y.val = n+v.val then 1
  else 1 / (10 * (arcs G univ).card)

private def restrictMinus {n : ℕ} (p : List (Fin (2*n))) : List (Fin n) :=
  p.filterMap (fun x => if h : x.val < n then some ⟨x.val,h⟩ else none)


/-- Aditya Anand, STOC 2027 submission #506 (October 2026), lemma 6 7. -/
theorem lemma_6_7 :
  DirectedCarvingPolyTime ∧
  ∀ (I : DirectedInput) (fs : List (DirectedFrame I.n)), DirectedRun I.G I.d I.s fs →
    fs.length ≤ I.n ∧
    (∀ f ∈ fs, (I.n : ℚ)/40 ≤ f.rho-f.w I.G I.d I.s ∧
      ((f.X I.d I.s).card : ℝ) ≤ 3*(I.n : ℝ)/4) ∧
    ∃ gs, DirectedRun I.G I.d I.s (fs++gs) ∧ DirectedComplete I.d I.s (fs++gs) := by sorry

end GreedyRegionGrowing.Layouts.Supplement
