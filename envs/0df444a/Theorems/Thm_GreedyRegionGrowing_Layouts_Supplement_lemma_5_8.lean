-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_Supplement_lemma_5_8
-- name    : GreedyRegionGrowing.Layouts.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:15.431122+00:00
-- url     : https://prove2.me/theorems/795c425b-e260-4aef-ab8a-4e167844f60d
-- title:
--   Lemma 5.8 — Weighted accounting
-- statement:
--   Under the same Section 5 assumptions and in every complete operational run of Algorithm 2, write U_i for the residual set, u_i for the selected center and r_i for its radius. All three accounting conclusions hold:
--
--   $$
--   \sum_i\operatorname{Vol}_{u_i}^{U_i}(r_i)\le2,\quad\sum_i A(X_i)=|A|,\quad\sum_i\frac{|\delta_G(X_i)|}{\Gamma(X_i)}\le3\sum_i\frac{|\delta_{G[U_i]}(X_i)|}{\Gamma(X_i)}.
--   $$
--
--   This is a supporting result for Theorem 1.5.
--
--   Differences from the source:
--   - encoding: finite labelled graphs, ordered iterations and polynomial-time algorithms → Fin n carriers, zero-based trace indices, fixed binary codes and deterministic TM2 polynomial time; reason: labels and iteration shifts change no source instance; the codes include all vertices and rational data, and the machine condition records the full runtime claim
--   - encoding: Section 5 edge lengths and shortest-path distances → symmetric nonnegative rational extensions to all pairs and a minimum over paths of at most n vertices; reason: only edge lengths enter valid paths; zero extension gives every source instance, and a shortest simple path exists under the connected nonnegative-length standing assumptions
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. Lemma 5.8, p. 28 (PDF p. 28).

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- §3.1 and Appendix D.3: exactly one commodity for each unordered pair. -/
private def pairs {n : ℕ} (U : Finset (Fin n)) := (U ×ˢ U).filter (fun p => p.1 < p.2)

private def IsDemand {n : ℕ} (U : Finset (Fin n)) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ u v, 0 ≤ D u v ∧ D u v = D v u) ∧ (∀ u, D u u = 0) ∧
  ∀ u v, u ∉ U ∨ v ∉ U → D u v = 0

private def Respects {n : ℕ} (U : Finset (Fin n)) (A : Fin n → ℚ)
    (D : Fin n → Fin n → ℝ) : Prop :=
  IsDemand U D ∧ ∀ u ∈ U, ∑ v ∈ U, D u v ≤ (A u : ℝ)

/-- Nonnegative flows in both edge orientations, with per-commodity conservation and total load.
No edge outside the induced component can carry a commodity. -/
private def Routable {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (D : Fin n → Fin n → ℝ) (q : ℝ) : Prop :=
  ∃ f : (Fin n × Fin n) → Fin n → Fin n → ℝ,
    (∀ p x y, 0 ≤ f p x y) ∧
    (∀ p x y, ¬ (x ∈ U ∧ y ∈ U ∧ G.Adj x y) → f p x y = 0) ∧
    (∀ p ∈ pairs U, ∀ x ∈ U,
      (∑ y ∈ U, (f p x y - f p y x)) =
        if x = p.1 then D p.1 p.2 else if x = p.2 then -D p.1 p.2 else 0) ∧
    ∀ e ∈ edges G U, ∑ p ∈ pairs U, (f p e.1 e.2 + f p e.2 e.1) ≤ q

private def FlowExpanding {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (A : Fin n → ℚ) (phi : ℚ) : Prop :=
  ∀ D, Respects U A D → Routable G U D (1/(phi : ℝ))

private def degreeWeight {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (u : Fin n) : ℚ :=
  (U.filter (fun v => G.Adj u v)).card

private def FlowExpander {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (phi : ℚ) :=
  FlowExpanding G U (degreeWeight G U) phi

private def weight {n : ℕ} (A : Fin n → ℚ) (U : Finset (Fin n)) : ℚ := ∑ v ∈ U, A v

private def productDemand {n : ℕ} (A : Fin n → ℚ) : Fin n → Fin n → ℝ := fun u v =>
  if u = v then 0 else (A u : ℝ) * (A v : ℝ) / (weight A univ : ℝ)

/-- Delete exactly the sorted unordered pairs of C. -/
private def remaining {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n × Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ (u,v) ∉ C ∧ (v,u) ∉ C
  symm := ⟨by intro u v h; exact ⟨G.symm.symm u v h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact G.loopless.irrefl u h.1⟩

private def nodeWeightCode {n : ℕ} (A : Fin n → ℚ) : Str :=
  (List.finRange n).flatMap (fun v => ratCode (A v))

private def edgeSetCode {n : ℕ} (C : Finset (Fin n × Fin n)) : Str :=
  listCode (fun e => natCode e.1.val ++ natCode e.2.val) (((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u,v)))).filter (fun e => decide (e ∈ C)))

/-- Output tag true certifies expansion; tag false carries the selected vertex set. -/
private def certificateCode {n : ℕ} (S : Option (Finset (Fin n))) : Str :=
  match S with
  | none => [true]
  | some X => [false] ++ setCode X

private def loglog (x : ℝ) : ℝ := max 1 (Real.log (Real.log x))

/-- Lengths of simple candidate walks, enumerated on the finite vertex set. -/
private def pathLength {n : ℕ} (ell : Fin n → Fin n → ℚ) : List (Fin n) → ℚ
  | [] => 0
  | [_] => 0
  | u::v::xs => ell u v + pathLength ell (v::xs)

private def pathLengths {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (u v : Fin n) : Finset ℚ :=
  ((range (n+1)).biUnion (fun k =>
    (univ : Finset (Fin k → Fin n)).image (fun f => List.ofFn f))).filter
      (fun p => p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.Adj) |>.image (pathLength ell)

/-- Nonnegative shortest-path metric. The minimum is over paths with at most n vertices;
zero is used only if no path exists, a case excluded by LengthInstance. -/
private def shortest {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (u v : Fin n) : ℚ :=
  let P := pathLengths G ell u v
  if h : P.Nonempty then P.min' h else 0

/-- Section 5 standing assumptions and (5.1); no rounding conclusion is assumed. -/
private def LengthInstance {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) : Prop :=
  G.Connected ∧ (∀ v, 1 ≤ A v) ∧ 0 < phi ∧
  (∀ u v, 0 ≤ ell u v ∧ ell u v = ell v u) ∧
  (∑ e ∈ edges G univ, ell e.1 e.2) ≤ 1 ∧
  (1/(2*(phi : ℝ))) < ∑ p ∈ pairs (univ : Finset (Fin n)),
    productDemand A p.1 p.2 * (shortest G ell p.1 p.2 : ℝ)

private def radiusR {n : ℕ} (A : Fin n → ℚ) (phi : ℚ) : ℚ := 1/(16*phi*weight A univ)

private def SmallBalls {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) : Prop :=
  ∀ u, weight A (ball (shortest G ell) univ u (radiusR A phi : ℝ)) < weight A univ / 3

private def weightedVolume {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
  let B := ball (shortest G ell) U u r
  (weight A B : ℝ)/(weight A univ : ℝ) +
    (∑ e ∈ edges G B, (ell e.1 e.2 : ℝ)) +
    ∑ e ∈ cut G U B, if e.1 ∈ B then r-(shortest G ell u e.1 : ℝ)
      else r-(shortest G ell u e.2 : ℝ)

private def deficitF {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) : ℝ :=
  Real.log (2*Real.exp 1 / weightedVolume G A ell U u r)

private def gamma {n : ℕ} (A : Fin n → ℚ) (S : Finset (Fin n)) : ℝ :=
  Real.log (Real.exp 1 * (weight A univ : ℝ)/(weight A S : ℝ))

private def kappa {n : ℕ} (A : Fin n → ℚ) : ℕ :=
  2 * (Int.ceil (Real.logb 2 (Real.log (2*Real.exp 1*(weight A univ : ℝ))))).toNat + 1

private def annulus {n : ℕ} (A : Fin n → ℚ) (phi : ℚ) (j : ℕ) : ℝ :=
  (radiusR A phi : ℝ) - j*(radiusR A phi : ℝ)/(2*kappa A)

private def Stable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (j : ℕ) : Prop :=
  deficitF G A ell U u (annulus A phi j) ≤ 2*deficitF G A ell U u (annulus A phi (j-1)) ∧
  gamma A (ball (shortest G ell) U u (annulus A phi j)) ≤
    2*gamma A (ball (shortest G ell) U u (annulus A phi (j-1)))

private structure WeightedFrame (n : ℕ) where
  U : Finset (Fin n)
  pointer : Fin n → ℕ
  center : Fin n
  radius : ℝ

namespace WeightedFrame
variable {n : ℕ}
private def X (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ) :=
  ball (shortest G ell) f.U f.center f.radius

private def V (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) := weightedVolume G A ell f.U f.center f.radius

/-- The while-loop increases a pointer through precisely the unstable annuli; no bound κ is imposed. -/
private def Operational (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) (old : Fin n → ℕ) : Prop :=
  f.center ∈ f.U ∧
  (∀ u ∈ f.U, old u ≤ f.pointer u ∧ Stable G A phi ell f.U u (f.pointer u) ∧
    ∀ j, old u ≤ j → j < f.pointer u → ¬ Stable G A phi ell f.U u j) ∧
  (∀ u ∈ f.U,
    weight A (ball (shortest G ell) f.U u (annulus A phi (f.pointer u-1))) ≤
    weight A (ball (shortest G ell) f.U f.center (annulus A phi (f.pointer f.center-1)))) ∧
  (let a := annulus A phi (f.pointer f.center)
   let b := annulus A phi (f.pointer f.center-1)
   a < f.radius ∧ f.radius < b ∧
   f.radius ∉ (f.U.image (fun v => (shortest G ell f.center v : ℝ))) ∧
   ((cut G f.U (f.X G ell)).card : ℝ) ≤ 4/(b-a)*f.V G A ell*
     deficitF G A ell f.U f.center f.radius)
end WeightedFrame

private def WeightedRunFrom {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) : Finset (Fin n) → (Fin n → ℕ) → List (WeightedFrame n) → Prop
  | _, _, [] => True
  | U, old, f::fs => f.U = U ∧ f.Operational G A phi ell old ∧
    WeightedRunFrom G A phi ell (U \ f.X G ell) f.pointer fs

private def WeightedRun {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) (fs : List (WeightedFrame n)) :=
  WeightedRunFrom G A phi ell univ (fun _ => 1) fs

private def WeightedComplete {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (fs : List (WeightedFrame n)) : Prop :=
  match fs.getLast? with
  | none => n = 0
  | some f => f.U \ f.X G ell = ∅

/-- Line 7 of Algorithm 2: every minimizing piece is an allowed returned set. -/
private def WeightedOutput {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (fs : List (WeightedFrame n)) (S : Finset (Fin n)) : Prop :=
  (∃ f ∈ fs, S = f.X G ell) ∧
  ∀ f ∈ fs, ((cut G univ S).card : ℝ)/((weight A S : ℝ)*gamma A S) ≤
    ((cut G univ (f.X G ell)).card : ℝ)/((weight A (f.X G ell) : ℝ)*gamma A (f.X G ell))

/-- Coded promise input for Lemmas 5.3 and 5.4, lengths included. -/
private structure RoundingInput where
  n : ℕ
  G : SimpleGraph (Fin n)
  A : Fin n → ℚ
  phi : ℚ
  ell : Fin n → Fin n → ℚ
  valid : LengthInstance G A phi ell

private def roundingCode (I : RoundingInput) : Str :=
  graphCode I.G ++ nodeWeightCode I.A ++ ratCode I.phi ++
    (List.finRange I.n).flatMap (fun u => (List.finRange I.n).flatMap (fun v => ratCode (I.ell u v)))

private structure HeavyInput extends RoundingInput where
  Y : Finset (Fin n)
  heavy : weight A univ / 3 ≤ weight A Y
  diameter : ∀ u ∈ Y, ∀ v ∈ Y, shortest G ell u v ≤ 2*radiusR A phi


/-- Aditya Anand, STOC 2027 submission #506 (October 2026), lemma 5 8. -/
theorem lemma_5_8 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) (hI : LengthInstance G A phi ell)
    (hsmall : SmallBalls G A phi ell) (fs : List (WeightedFrame n))
    (hr : WeightedRun G A phi ell fs) (hc : WeightedComplete G ell fs) :
  (fs.map (fun f => f.V G A ell)).sum ≤ 2 ∧
  (fs.map (fun f => weight A (f.X G ell))).sum = weight A univ ∧
  (fs.map (fun f => ((cut G univ (f.X G ell)).card : ℝ)/gamma A (f.X G ell))).sum ≤
    3*(fs.map (fun f => ((cut G f.U (f.X G ell)).card : ℝ)/gamma A (f.X G ell))).sum := by sorry

end GreedyRegionGrowing.Layouts.Supplement
