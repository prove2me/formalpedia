-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_proposition_4_15
-- name    : LimitsLifting.Approximation.proposition_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:00.048233+00:00
-- url     : https://prove2.me/theorems/48bb576d-3a2c-43c9-a631-5ce313f36b12
-- title:
--   Proposition 4.15 — leaves and non-leaves of the rectangle circuit $\Pi_B$
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs and no clause is tautological, let $m\ge1$, let $\sigma$ be a Rectangle Scheme with constant $K$ and let $0<w\le n$. Let $B$ be a monotone $\{\bar\vee,\bar\wedge\}$-circuit over the inputs $x_{(C,\alpha)}$ from which all constants have been removed (no constant operand, and no gate computes a constant function on $\mathcal Z_{m,n}$), whose final rectangle is $\gamma$-dense for some $\gamma>0$. Then:
--   1. **Leaves.** Each leaf $x_{(C,\alpha)}$ of $\Pi_B$ has rectangle $R_{x_{(C,\alpha)}}=R_{C,\alpha}\in\mathcal R$.
--   2. **Non-leaves.** For each gate $g$ of $B$ with children $h,h'$, every structured piece produced by the Rectangle Scheme (parameter $w$) on $R_g^*=R_{h\circ h'}$ is contained in the union of the structured subrectangles of $R_h^*$ and $R_{h'}^*$.
--
--   Here the structured subrectangles of a gate node are the scheme's structured pieces on its rectangle $R^*$, and the structured subrectangle of a leaf $x_{(C,\alpha)}$ is $R_{C,\alpha}$ itself, with the restriction $\rho$ that falsifies $C$, as the source states on printed pp. 23–24.
--
--   These are the two invariants along which the simulation proof of Lemma 4.10 walks down the rectangle circuit.
--
--   **Formalization Note** "Ω(1)-dense" is read as $\gamma$-dense for an arbitrary $\gamma>0$. The circuit is a well-formed straight-line program over the coordinates of the canonical cover.
--
--   Differences from the source:
--   - reading: the structured subrectangles of a leaf child R_{C,α}, i.e. the output of the Rectangle Scheme on R_{C,α}, which the source states is R_{C,α} itself → the single piece R_{C,α} with the restriction falsifying C; reason: the source identifies the scheme's output on R_{C,α} with R_{C,α} (printed p.23, and the proof of item 1 on p.24); in M_w leaves are never passed through the scheme, and Lemma 4.7's listed properties alone do not force this identity (a scheme with those properties may declare a unit-clause input rectangle an error row), so the leaf's piece is taken as the source describes it.
--   - reading: a {∨̄,∧̄}-circuit after the removal of all constants → a circuit with no constant operand none of whose gates computes a constant function; reason: §4.4 removes constants before defining Π_B, and Definition 4.9 applies the exact gate whenever an argument is a constant function, so these are the circuits on which R_g^* is defined.
--   - generalization: the Rectangle Scheme of [GGKS20] with m = n^Δ → every deterministic scheme with the properties of Lemma 4.7 and every m ≥ 1; reason: the source states only these properties of the scheme ("We merely state the properties of the algorithm that we will use", printed p.20) and its proofs use only them; in M_w the scheme is applied only at gates, never to the input leaves (Definition 4.9); the [GGKS20] scheme has these properties (Lemma 4.7), so the statement specializes to the source's.
--   - generalization: a final rectangle of Ω(1) density on both sides → a final rectangle of any positive density γ, even if γ depends on n or F; reason: every source instance has a fixed positive density, which is a special case; the conclusions do not depend on the density.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Proposition 4.15, printed p. 24 (PDF p. 25); rectangle circuits §4.4, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem proposition_4_15 {n m : ℕ} (hm : 1 ≤ m) (K : ℝ) (σ : RectScheme n m)
    (hσ : IsRectangleScheme n m K σ) (F : CNF (Fin n)) (hF : StandingCNF F)
    (w : ℝ) (hw0 : 0 < w) (hwn : w ≤ n) (γ : ℝ) (hγ : 0 < γ)
    (B : Circuit (Coord m F)) (hWF : B.WellFormed) (hmono : B.IsMonotone)
    (hcf : B.ConstantFree) (hnc : NoConstantGates σ w B)
    (hdense : RectDense γ (rectOf (approxOutput σ w B))) :
    -- 1. Leaves: every leaf `x_{(C,α)}` of `Π_B` has rectangle `R_{C,α}`.
    (∀ (c : Coord m F) (b : Bool),
      ((∃ g ∈ B.gates, g.2.1 = .lit c b ∨ g.2.2 = .lit c b) ∨ B.output = .lit c b) →
        rectOf (inputFn c) = canonRect c) ∧
    -- 2. Non-leaves: each structured piece of the scheme on `R_g^*` lies in the union of the
    --    structured subrectangles of the two children.
    (∀ (k : ℕ) (hk : k < B.gates.length),
      ∀ p ∈ (σ w (gateStar σ w B k).1 (gateStar σ w B k).2).structured,
        ∀ x ∈ p.2.1, ∀ y ∈ p.2.2,
          ∃ q, (q ∈ nodeStructuredPieces σ w B (B.gates[k]).2.1 ∨
              q ∈ nodeStructuredPieces σ w B (B.gates[k]).2.2) ∧
            x ∈ q.2.1 ∧ y ∈ q.2.2) := by sorry

end LimitsLifting.Approximation
