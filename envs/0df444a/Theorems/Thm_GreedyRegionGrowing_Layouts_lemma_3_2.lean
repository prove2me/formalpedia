-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_lemma_3_2
-- name    : GreedyRegionGrowing.Layouts.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:31:32.363306+00:00
-- url     : https://prove2.me/theorems/9acf02bf-76d2-493e-8252-ea5e9bc57124
-- title:
--   Lemma 3.2 — Line metrics satisfy spreading
-- statement:
--   Let $V$ be a finite set, let $\pi$ bijectively assign its vertices to distinct consecutive integer positions, let $u\in V$, and let $S\subseteq V$. Then
--   $$\sum_{v\in S}|\pi(u)-\pi(v)|\ge\frac{|S|^2-1}{4}.$$
--   This supplies the spreading inequalities for line distances of orderings, including empty subsets.
--
--   Differences from the source:
--   - encoding: finite vertex sets, induced instances, and mathematical objects → Fin n labels, a finite carrier A, explicit lists and concrete predicates; reason: relabeling preserves every source instance; cut and separation empty maxima are zero, and bag widths are integers
-- source:
--   Aditya Anand, STOC 2027 submission #506 (October 2026), Lemma 3.2, p. 18 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/506.pdf

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_SNPTreedepth_treedepth

noncomputable section
open Finset
open QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts
attribute [local instance] Classical.propDecidable

open Finset
open QAlgorithms.Complexity



/-- Source §3.2, pp.17–18. A list contains each vertex exactly once. -/
private def IsOrdering {n : ℕ} (A : Finset (Fin n)) (π : List (Fin n)) : Prop :=
  π.Nodup ∧ π.toFinset = A

private def orderingPrefix {n : ℕ} (π : List (Fin n)) (i : ℕ) : Finset (Fin n) :=
  (π.take i).toFinset

/-- Each unordered edge is represented once, with its smaller label first. -/
private def edges {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (A ×ˢ A).filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

private def cut {n : ℕ} (G : SimpleGraph (Fin n)) (A S : Finset (Fin n)) :=
  (edges G A).filter (fun e => (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ e.1 ∉ S))

private def active {n : ℕ} (G : SimpleGraph (Fin n)) (A S : Finset (Fin n)) :=
  S.filter (fun v => ∃ w ∈ A \ S, G.Adj v w)

private def orderingCutwidth {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (π : List (Fin n)) : ℕ :=
  (range (π.length + 1)).sup (fun i => (cut G A (orderingPrefix π i)).card)

private def separation {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (π : List (Fin n)) : ℕ :=
  (range (π.length + 1)).sup (fun i => (active G A (orderingPrefix π i)).card)

/-- The minimum ranges over every ordering, including the empty ordering. -/
private def cutwidth {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  sInf {k | ∃ π, IsOrdering A π ∧ orderingCutwidth G A π = k}

private def minSeparation {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  sInf {k | ∃ π, IsOrdering A π ∧ separation G A π = k}

private def pw {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℤ :=
  GaussianSweep.pathwidth (G.induce (↑A : Set (Fin n)))

/-- Bag lists use the published decomposition axioms; all bags lie in A. -/
private def IsDecomposition {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (B : List (Finset (Fin n))) : Prop :=
  (∀ b ∈ B, b ⊆ A) ∧
  GaussianSweep.IsPathDecomposition (G.induce (↑A : Set (Fin n))) B.length
    (fun i => (B.get i).subtype (fun v => v ∈ A))

private def bagWidth {n : ℕ} (B : List (Finset (Fin n))) : ℤ :=
  ((B.map Finset.card).foldl max 0 : ℕ) - (1 : ℤ)

/-- The explicit bags in Lemma 3.1; the empty graph uses one empty bag. -/
private def orderingBags {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (π : List (Fin n)) : List (Finset (Fin n)) :=
  if π = [] then [∅] else
  (List.range π.length).map (fun i =>
    ((π.drop i).take 1).toFinset ∪ active G A (orderingPrefix π i))

/-- Equation (4.1), including the negative right side for an empty S. -/
private def Spreading {n : ℕ} (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) : Prop :=
  (∀ u ∈ A, d u u = 0) ∧
  (∀ u ∈ A, ∀ v ∈ A, 0 ≤ d u v ∧ d u v = d v u) ∧
  (∀ u ∈ A, ∀ v ∈ A, ∀ w ∈ A, d u w ≤ d u v + d v w) ∧
  (∀ u ∈ A, ∀ S : Finset (Fin n), S ⊆ A →
    ((S.card : ℚ)^2 - 1) / 4 ≤ ∑ v ∈ S, d u v)

private def edgeObjective {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) : ℚ := ∑ e ∈ edges G A, d e.1 e.2

private def VertexFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) : Prop :=
  Spreading A d ∧ (∀ v ∈ A, 0 ≤ x v) ∧
    (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → d u v ≤ x u + x v)

private def vertexObjective {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℚ) : ℚ := ∑ v ∈ A, x v

/-- Finite rational LPs: these sets are nonempty, bounded below, and attain a rational minimum.
The real infimum is used only for values, never to implement an algorithm. -/
private def edgeLP {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℝ :=
  sInf {r | ∃ d, Spreading A d ∧ r = (edgeObjective G A d : ℝ)}

private def vertexLP {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℝ :=
  sInf {r | ∃ d x, VertexFeasible G A d x ∧ r = (vertexObjective A x : ℝ)}

private def EdgeOptimal {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) : Prop :=
  Spreading A d ∧ ∀ d', Spreading A d' → edgeObjective G A d ≤ edgeObjective G A d'

private def VertexOptimal {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) : Prop :=
  VertexFeasible G A d x ∧ ∀ d' x', VertexFeasible G A d' x' →
    vertexObjective A x ≤ vertexObjective A x'

private def ConnectedInstance {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  2 ≤ A.card ∧ (G.induce (↑A : Set (Fin n))).Connected

/-- The graph header is unary n followed by a zero, then n² adjacency bits in row order.
This includes isolated vertices and has exactly n+1+n² bits. -/
private def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) : Str :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => decide (G.Adj u v)))

/-- Self delimiting binary naturals: unary bit length, zero, then little endian digits. -/
private def natCode (k : ℕ) : Str :=
  let b := (Nat.digits 2 k).map (fun i => decide (i = 1))
  List.replicate b.length true ++ [false] ++ b

private def listCode {α : Type} (enc : α → Str) (l : List α) : Str :=
  natCode l.length ++ l.flatMap enc

private def orderingCode {n : ℕ} (π : List (Fin n)) : Str := listCode (fun v => natCode v.val) π

private def setCode {n : ℕ} (A : Finset (Fin n)) : Str := orderingCode (A.sort (· ≤ ·))

private def bagsCode {n : ℕ} (B : List (Finset (Fin n))) : Str := listCode setCode B

private def ratCode (q : ℚ) : Str := [decide (q < 0)] ++ natCode q.num.natAbs ++ natCode q.den

/-- Concrete length-orderingPrefixed decoder, rejecting an incomplete code. -/
private def readNat (s : Str) : Option (ℕ × Str) := do
  let h := s.takeWhile id
  let tail := s.drop h.length
  if tail.head? != some false then none else do
    let t := tail.drop 1
    if t.length < h.length then none else
      some (((t.take h.length).reverse.foldl (fun a b => 2*a + if b then 1 else 0) 0), t.drop h.length)

private def readList {α : Type} (read : Str → Option (α × Str)) : ℕ → Str → Option (List α × Str)
  | 0, s => some ([], s)
  | k+1, s => do
      let (a,t) ← read s
      let (l,u) ← readList read k t
      some (a::l,u)

private def readNatList (s : Str) : Option (List ℕ × Str) := do
  let (k,t) ← readNat s
  readList readNat k t

/-- Output decoding is explicit; validity is checked against the graph in the theorems. -/
private def decodeOrdering (n : ℕ) (s : Str) : Option (List (Fin n)) := do
  let (l,t) ← readNatList s
  if t != [] then none else l.mapM (fun v => if h : v < n then some ⟨v,h⟩ else none)

private def decodeBags (n : ℕ) (s : Str) : Option (List (Finset (Fin n))) := do
  let (k,t) ← readNat s
  let (ll,u) ← readList readNatList k t
  if u != [] then none else
    ll.mapM (fun l => do
      let vs ← l.mapM (fun v => if h : v < n then some (⟨v,h⟩ : Fin n) else none)
      some vs.toFinset)

/-- The full-strength headline guarantee, with actual output decoding. -/
private def LayoutGuarantee (fc fp : Str → Str) (Cc Cp : ℝ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ π B,
    decodeOrdering n (fc (graphCode G)) = some π ∧
    decodeBags n (fp (graphCode G)) = some B ∧
    IsOrdering univ π ∧ IsDecomposition G univ B ∧
    (n ≤ 1 → orderingCutwidth G univ π = 0 ∧
      bagWidth B = (if n = 0 then -1 else 0)) ∧
    (2 ≤ n → (orderingCutwidth G univ π : ℝ) ≤ Cc * Real.log n * cutwidth G univ ∧
      (bagWidth B : ℝ) ≤ Cp * Real.log n * (pw G univ : ℝ))

open Finset



/-- Equations (4.3), (4.5), and §7.2, pp.20–21,35. -/
private def ball {n : ℕ} (d : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) :=
  U.filter (fun v => (d u v : ℝ) < r)

private def core {n : ℕ} (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (U : Finset (Fin n)) (u : Fin n) (r : ℝ) :=
  U.filter (fun v => (d u v : ℝ) + (x v : ℝ) < r)

private def separator {n : ℕ} (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (U : Finset (Fin n)) (u : Fin n) (r : ℝ) :=
  U.filter (fun v => (d u v : ℝ) - (x v : ℝ) < r ∧ r < (d u v : ℝ) + (x v : ℝ))

private def setVolume {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (S : Finset (Fin n)) : ℚ :=
  edgeObjective G A d * S.card / A.card + edgeObjective G S d

private def edgeVolume {n : ℕ} (G : SimpleGraph (Fin n)) (A U : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (u : Fin n) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
  let B := ball d U u r
  (setVolume G A d B : ℝ) + ∑ e ∈ cut G U B,
    (if e.1 ∈ B then r - (d u e.1 : ℝ) else r - (d u e.2 : ℝ))

private def vertexVolume {n : ℕ} (A U : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) (u : Fin n) (r : ℝ) : ℝ :=
  (vertexObjective A x : ℝ) * (ball d U u r).card / A.card +
    ∑ v ∈ U, min (2 * (x v : ℝ)) (max 0 (r - (d u v : ℝ) + (x v : ℝ)))

/-- The finite event sets retain events even when a boundary does not change. -/
private def events {n : ℕ} (vertex : Bool) (U : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) (u : Fin n) : Finset ℚ :=
  U.image (d u) ∪ if vertex then
    U.image (fun v => d u v - x v) ∪ U.image (fun v => d u v + x v) else ∅

/-- §3.3, p.18. Monotonicity allows upward jumps. Affine on every event-free interval. -/
private def VolumeFunction (V c : ℝ → ℝ) (E : Finset ℝ) (Λ : ℝ) : Prop :=
  (∀ r, 0 < r → 0 < V r ∧ V r ≤ Λ) ∧
  MonotoneOn V (Set.Ioi 0) ∧
  (∀ a b, 0 < a → a < b → (∀ e ∈ E, e ∉ Set.Ioo a b) →
    ∃ m q : ℝ, ∀ r ∈ Set.Ioo a b, V r = m*r+q) ∧
  (∀ r, 0 < r → r ∉ E → 0 ≤ c r ∧ HasDerivAt V (c r) r)

/-- Rational evaluation used by Algorithms 1 and 4. -/
private def carvingVolume {n : ℕ} (vertex : Bool) (G : SimpleGraph (Fin n))
    (A U : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (u : Fin n) (r : ℚ) : ℚ :=
  if vertex then
    vertexObjective A x * (ball d U u (r : ℝ)).card / A.card +
      ∑ v ∈ U, min (2*x v) (max 0 (r-d u v+x v))
  else if r ≤ 0 then 0 else
    let B := ball d U u (r : ℝ)
    setVolume G A d B + ∑ e ∈ cut G U B,
      (if e.1 ∈ B then r-d u e.1 else r-d u e.2)

private def carvingCore {n : ℕ} (vertex : Bool) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (U : Finset (Fin n)) (u : Fin n) (r : ℚ) : Finset (Fin n) :=
  if vertex then core d x U u r else ball d U u r

private def carvingSeparator {n : ℕ} (vertex : Bool) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (U : Finset (Fin n)) (u : Fin n) (r : ℚ) : Finset (Fin n) :=
  if vertex then separator d x U u r else ∅

private def carvingCost {n : ℕ} (vertex : Bool) (G : SimpleGraph (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℚ) : ℕ :=
  if vertex then (separator d x U u r).card else (cut G U (ball d U u r)).card

/-- Operational frame only: no success, size, radius or prefix inequality is assumed. -/
private structure CarveFrame (n : ℕ) where
  U : Finset (Fin n)
  rho : ℚ
  center : Fin n
  radius : ℚ

namespace CarveFrame
variable {n : ℕ}

private def K (f : CarveFrame n) (vertex : Bool) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) : ℚ :=
  ((f.U.sort (· ≤ ·)).map (fun u => carvingVolume vertex G A f.U d x u f.rho)).foldl max 0

private def w (f : CarveFrame n) (vertex : Bool) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) : ℚ :=
  A.card * f.K vertex G A d x /
    ((if vertex then 240 else 160) * (if vertex then vertexObjective A x else edgeObjective G A d))

private def S (f : CarveFrame n) (vertex : Bool) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) :=
  carvingCore vertex d x f.U f.center f.radius

private def D (f : CarveFrame n) (vertex : Bool) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) :=
  carvingSeparator vertex d x f.U f.center f.radius

private def nextU (f : CarveFrame n) (vertex : Bool) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) :=
  f.U \ (f.S vertex d x ∪ f.D vertex d x)

private def W (f : CarveFrame n) (vertex : Bool) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) :=
  carvingVolume vertex G A f.U d x f.center f.radius

/-- Lines 4–5 of Algorithms 1 and 4 (pp.22, 36): `center` is any vertex of `U` maximizing the
volume at the inner radius `ρ − w`, and `radius` is any radius of the open window `(ρ − w, ρ)` that is
not an event of the center's volume and minimizes the boundary cost (edge boundary in `G[U]`, resp.
separator size) among all such radii. Radii are rational, as all algorithmic parameters (§3, p.17). -/
private def Operational (f : CarveFrame n) (vertex : Bool) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) : Prop :=
  f.center ∈ f.U ∧
  (let a := f.rho - f.w vertex G A d x
   let v := fun u => carvingVolume vertex G A f.U d x u a
   let E := events vertex f.U d x f.center
   let c := carvingCost vertex G d x f.U f.center
   (∀ u ∈ f.U, v u ≤ v f.center) ∧
   a < f.radius ∧ f.radius < f.rho ∧ f.radius ∉ E ∧
   (∀ r : ℚ, a < r → r < f.rho → r ∉ E → c f.radius ≤ c r))
end CarveFrame

/-- Finite operational trace; it may stop with a nonempty residual. Completion is a theorem. -/
private def RunFrom {n : ℕ} (vertex : Bool) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) :
    Finset (Fin n) → ℚ → List (CarveFrame n) → Prop
  | _, _, [] => True
  | U, rho, f::fs => f.U = U ∧ f.rho = rho ∧ f.Operational vertex G A d x ∧
      RunFrom vertex G A d x (f.nextU vertex d x) (rho-f.w vertex G A d x) fs

private def IsRun {n : ℕ} (vertex : Bool) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ) (fs : List (CarveFrame n)) : Prop :=
  RunFrom vertex G A d x A (A.card/10) fs

private def Complete {n : ℕ} (vertex : Bool) (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ)
    (x : Fin n → ℚ) (fs : List (CarveFrame n)) : Prop :=
  match fs.getLast? with
  | none => A = ∅
  | some f => f.nextU vertex d x = ∅

/-- Ordered pieces, not an unordered partition; every piece is nonempty. -/
private def WeakPartition {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (d : Fin n → Fin n → ℚ) (α : ℝ) (Xs : List (Finset (Fin n))) : Prop :=
  (∀ X ∈ Xs, X.Nonempty ∧ X ⊆ A ∧ (X.card : ℝ) ≤ A.card/2) ∧
  Xs.Pairwise Disjoint ∧ Xs.foldl (· ∪ ·) ∅ = A ∧
  ∀ i : Fin Xs.length,
    (∑ X ∈ (Xs.take (i.val+1)).toFinset, (cut G A X).card : ℝ) ≤
      α * (edgeObjective G A d : ℝ) / A.card *
      Real.log (2 * Real.exp 1 * (edgeObjective G A d : ℝ) / (setVolume G A d (Xs.get i) : ℝ))

open Finset
open QAlgorithms.Complexity



/-- Full binary rational input to the carver; optimality is part of the source's local input only. -/
private structure CarvingInput (vertex : Bool) where
  n : ℕ
  G : SimpleGraph (Fin n)
  A : Finset (Fin n)
  d : Fin n → Fin n → ℚ
  x : Fin n → ℚ
  connected : ConnectedInstance G A
  optimal : if vertex then VertexOptimal G A d x else EdgeOptimal G A d

private def carvingInputCode {vertex : Bool} (I : CarvingInput vertex) : Str :=
  graphCode I.G ++ setCode I.A ++
  (List.finRange I.n).flatMap (fun u => (List.finRange I.n).flatMap (fun v => ratCode (I.d u v))) ++
  (List.finRange I.n).flatMap (fun v => ratCode (I.x v))

private def frameCode {n : ℕ} (f : CarveFrame n) : Str :=
  setCode f.U ++ ratCode f.rho ++ natCode f.center.val ++ ratCode f.radius

private def runCode {n : ℕ} (fs : List (CarveFrame n)) := listCode frameCode fs

/-- A single machine realizes complete runs for all labelled instances and all rational input lengths. -/
private def CarvingPolyTime (vertex : Bool) : Prop :=
  ∃ F : (I : CarvingInput vertex) → List (CarveFrame I.n),
    PPSLattice.PolyTimeOn carvingInputCode (fun I => runCode (F I)) ∧
    ∀ I, IsRun vertex I.G I.A I.d I.x (F I) ∧ Complete vertex I.A I.d I.x (F I)

/-- The hypothesis of Lemma 4.2 (p.20): one deterministic polynomial-time machine that, given a
connected induced instance `G[A]` with at least two vertices, returns an ordered partition that is an
`α`-weak local partition (Definition 4.1) with respect to some optimal solution `d` of (4.1) on that
instance. The procedure is not handed `d`; it may compute one itself. -/
private def WeakPartitionProcedure (α : ℝ) : Prop :=
  ∃ F : (I : Σ n, SimpleGraph (Fin n) × Finset (Fin n)) → List (Finset (Fin I.1)),
    PPSLattice.PolyTimeOn (fun I => graphCode I.2.1 ++ setCode I.2.2)
      (fun I => listCode setCode (F I)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), ConnectedInstance G A →
      ∃ d, EdgeOptimal G A d ∧ WeakPartition G A d α (F ⟨n, (G, A)⟩)

/-- Uniform cutwidth approximation, with exact small inputs and an actual decoded ordering. -/
private def CutwidthApproximation (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ π,
      decodeOrdering n (f (graphCode G)) = some π ∧ IsOrdering univ π ∧
      (n ≤ 1 → orderingCutwidth G univ π = 0) ∧
      (2 ≤ n → (orderingCutwidth G univ π : ℝ) ≤
        C * α * Real.log n * cutwidth G univ)

/-- Maximal connected vertex sets of an induced graph, without an enumeration oracle. -/
private def components {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  A.powerset.filter (fun C => C.Nonempty ∧ (G.induce (↑C : Set (Fin n))).Connected ∧
    ∀ u ∈ C, ∀ v ∈ A \ C, ¬ G.Adj u v)

private def componentList {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : List (Finset (Fin n)) :=
  (components G A).toList.mergeSort (fun C C' => decide
    ((∑ v ∈ C, (2 : ℕ)^v.val) ≤ ∑ v ∈ C', (2 : ℕ)^v.val))

private abbrev Parent (n : ℕ) := Fin n → Option (Fin n)

private def parentAt {n : ℕ} (p : Parent n) (v : Fin n) (k : ℕ) : Option (Fin n) :=
  (fun q : Option (Fin n) => q.bind p)^[k] (some v)

/-- An elimination forest uses the published acyclic parent/depth model on exactly A. -/
private def EliminationForest {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (p : Parent n) : Prop :=
  (∀ v, v ∉ A → p v = none) ∧
  ∃ F : SNPTreedepth.RootedForest {v // v ∈ A},
    (∀ v, (F.parent v).map Subtype.val = p v.val) ∧
    ∀ u v, G.Adj u.val v.val → F.IsAncestor u v ∨ F.IsAncestor v u

private def forestHeight {n : ℕ} (A : Finset (Fin n)) (p : Parent n) : ℕ :=
  A.sup (fun v => ((List.range n).filter (fun k => (parentAt p v k).isSome)).length)

private def treedepth {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  sInf {h | ∃ p, EliminationForest G A p ∧ forestHeight A p = h}

private def dfsNode {n : ℕ} (A : Finset (Fin n)) (p : Parent n) : ℕ → Fin n → List (Fin n)
  | 0, _ => []
  | k+1, v => v :: ((A.filter (fun w => p w = some v)).sort (· ≤ ·)).flatMap (dfsNode A p k)

/-- Actual recursive preorder with roots and children in label order. -/
private def dfs {n : ℕ} (A : Finset (Fin n)) (p : Parent n) : List (Fin n) :=
  ((A.filter (fun v => p v = none)).sort (· ≤ ·)).flatMap (dfsNode A p n)

/-- The vertices of `A` below `v` in the forest `p`, `v` included. -/
private def descendants {n : ℕ} (A : Finset (Fin n)) (p : Parent n) (v : Fin n) : Finset (Fin n) :=
  A.filter (fun w => ∃ k, parentAt p w k = some v)

/-- A depth-first preorder of the forest `p` on `A` (Lemma 7.2, p.34), for any order of roots and
of children: an ordering of `A` in which the subtree of every vertex is a contiguous block that
starts with that vertex. -/
private def IsDFSPreorder {n : ℕ} (A : Finset (Fin n)) (p : Parent n) (π : List (Fin n)) : Prop :=
  IsOrdering A π ∧ ∀ v ∈ A, ∃ i, π[i]? = some v ∧
    ((π.drop i).take (descendants A p v).card).toFinset = descendants A p v

private def parentCode {n : ℕ} (p : Parent n) : Str :=
  (List.finRange n).flatMap (fun v => match p v with
    | none => [false]
    | some w => [true] ++ natCode w.val)

/-- Disjoint union and a separator chain. All roots of children hang below the last chain label. -/
private def glue {n : ℕ} (D : Finset (Fin n)) (children : List (Finset (Fin n) × Parent n)) : Parent n :=
  let chain := D.sort (· ≤ ·)
  fun v => if v ∈ D then
      match chain.idxOf v with
      | 0 => none
      | k+1 => chain[k]?
    else match children.find? (fun cp => decide (v ∈ cp.1)) with
      | none => none
      | some cp => match cp.2 v with
        | some w => some w
        | none => chain.getLast?

/-- Backward assembly of §7.5, not an assumed height guarantee. -/
private def assemble {n : ℕ} (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (child : Finset (Fin n) → Parent n) (G : SimpleGraph (Fin n)) :
    List (CarveFrame n) → Parent n
  | [] => fun _ => none
  | f::fs => glue (f.D true d x)
      ((f.nextU true d x, assemble d x child G fs) ::
        (componentList G (f.S true d x)).map
          (fun C => (C, child C)))

/-- Finite derivations of the exact recursive construction. LP feasibility/optimality is a choice
of data at each node; its polynomial computation is asserted separately, never assumed. -/
private inductive ForestConstruction {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) → Parent n → Prop
  | empty : ForestConstruction G ∅ (fun _ => none)
  | singleton (v : Fin n) : ForestConstruction G {v} (fun _ => none)
  | split (A : Finset (Fin n)) (child : Finset (Fin n) → Parent n)
      (h : ¬ (G.induce (↑A : Set (Fin n))).Connected)
      (hc : ∀ C ∈ components G A, ForestConstruction G C (child C)) :
      ForestConstruction G A (glue ∅ ((componentList G A).map
        (fun C => (C, child C))))
  | carve (A : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
      (fs : List (CarveFrame n)) (child : Finset (Fin n) → Parent n)
      (hA : ConnectedInstance G A) (ho : VertexOptimal G A d x)
      (hr : IsRun true G A d x fs) (hdone : Complete true A d x fs)
      (hc : ∀ f ∈ fs, ∀ C ∈ components G (f.S true d x), ForestConstruction G C (child C)) :
      ForestConstruction G A (assemble d x child G fs)

/-- Graph input alone; the machine must compute LP solutions and finish all recursion. -/
private def ForestConstructionPolyTime : Prop :=
  ∃ F : (n : ℕ) → SimpleGraph (Fin n) → Parent n,
    PPSLattice.PolyTimeOn (fun I : Σ n, SimpleGraph (Fin n) => graphCode I.2)
      (fun I => parentCode (F I.1 I.2)) ∧
    ∀ n G, ForestConstruction G univ (F n G)

private def assemblyBound {n : ℕ} (G : SimpleGraph (Fin n)) (d : Fin n → Fin n → ℚ)
    (x : Fin n → ℚ) (fs : List (CarveFrame n)) (child : Finset (Fin n) → Parent n) : ℕ :=
  ((fs.zipIdx).map (fun fi =>
    ((fs.take (fi.2+1)).map (fun f => (f.D true d x).card)).sum +
    (components G (fi.1.S true d x)).sup (fun C => forestHeight C (child C)))).foldl max 0

theorem lemma_3_2 {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n) (S : Finset (Fin n)) :
  ((S.card : ℚ)^2 - 1)/4 ≤ ∑ v ∈ S, |(π u).val - ((π v).val : ℚ)| := by sorry

end GreedyRegionGrowing.Layouts
