-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_theorem_5_1
-- name    : FullRankSmallSetQLTC.IndependentChecks.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:37.433488+00:00
-- url     : https://prove2.me/theorems/1363b0f9-874a-41fe-a443-61a56dace219
-- title:
--   Theorem 5.1 — lossless line products with a free 2-group action
-- statement:
--   Let $t\ge1$ be an integer and $\varepsilon\in(0,1)$. There is $d_0$ such that for every integer $d\ge d_0$ there are a power of two $h\ge2$, two disjoint lists $P^L,P^R$ of $h$ primes congruent to $1$ modulo $8$, an integer $D_R>d$, a constant $c>0$ and an integer $m_0\ge3$ satisfying (4.5) for the union, with the following property. For $m\ge m_0$ let $Y_L,Y_R$ be the complexes of Theorem 4.6 on $G_m$ for $P^L$ and $P^R$. There are signature sets $S_L,S_R$ with $|S_L|=tD_R$ and $|S_R|=D_R$ and a gadget $C$ of degrees $(d,td)$ such that $Z_0=Z(I(Y_L,S_L),I(Y_R,S_R);C)$ satisfies:
--
--   1. $Z_0$ is simple, $(hd,htd)$-biregular and two-sided $(c,\varepsilon)$-lossless;
--   2. $Z_0$ satisfies the distinct-witness condition (3.2);
--   3. left translation is a free action of the 2-group $G_m$, with $|S_L|$, $|S_R|$ and $h$ orbits on $L$, $R$ and $M$;
--   4. the sets $S_L,S_R$, the gadget $C$ and the neighbours of a vertex of $Z_0$ are computable in time polynomial in $m$.
--
--   Differences from the source:
--   - encoding: signature sets S_L, S_R of sizes tD_R, D_R; vertex sets G_m × S_L, G_m × S_R → injective enumerations [tD_R] → signatures, [D_R] → signatures; vertex sets G_m × [tD_R], G_m × [D_R]; reason: a finite set of the given size is the image of an injective enumeration; the vertex sets correspond bijectively
--   - encoding: for m ≥ m₀ there are S_L, S_R, C (and they are computable in time polynomial in m) → families m ↦ S_L(m), S_R(m), C(m) chosen before the machines, with fixed machines computing the signature tables, the gadget table and the neighbour lists (both directions, on normal-form codes) for all m ≥ m₀; reason: computability in time polynomial in m is a uniform statement about the choices for all m; per-m choices without uniformity would make the clause meaningless
--   - encoding: left translation is a free action on Z₀ → left translation is free on L, R and M and preserves the edges of Z₀; reason: an action on a graph preserves its edges
--   - encoding: a power of two h ≥ 2; disjoint lists of h primes → h = 2^k with k ≥ 1; the 2h primes are pairwise distinct; reason: Theorem 4.6, applied to each list and to the union in (4.5), concerns distinct primes
--   - encoding: for m ≥ m₀, the complexes of Theorem 4.6 for P^L and P^R → 3 ≤ m₀ and 2√((∏ P^L)(∏ P^R)) < 2^m₀, followed by all the stated properties for m ≥ m₀; reason: Definition 4.1 requires m ≥ 3 and Theorem 4.6 requires (4.5); p. 24 chooses m₀ as the least m ≥ 3 satisfying (4.5) for the union, and separation persists for larger m
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 5.1, p. 24 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Explicit
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Cubical

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction

open Classical in
/-- **Theorem 5.1** (Lossless line products with a free 2-group action, p. 24). Let `t ≥ 1` be an
integer and `ε ∈ (0, 1)`. There is `d₀` such that for every integer `d ≥ d₀` there are a power of
two `h = 2^k ≥ 2`, two disjoint lists `P^L`, `P^R` of `h` (distinct) primes `≡ 1 (mod 8)`, an
integer `D_R > d`, a constant `c > 0` and an integer `m₀ ≥ 3` satisfying (4.5) for the union
of the prime lists, such that, for `m ≥ m₀`, with
`Y_L`, `Y_R` the complexes of Theorem 4.6 on `G_m` for `P^L`, `P^R`, there are signature sets
`S_L`, `S_R` with `|S_L| = tD_R`, `|S_R| = D_R` (enumerated injectively by `[tD_R]`, `[D_R]`) and a
gadget `C` of degrees `(d, td)`, such that `Z₀ = Z(I(Y_L, S_L), I(Y_R, S_R); C)` satisfies:
1. `Z₀` is simple, `(hd, htd)`-biregular and two-sided `(c, ε)`-lossless;
2. `Z₀` satisfies the distinct-witness condition (3.2);
3. left translation is a free action of the 2-group `G_m` (preserving the edges), with `|S_L|`,
   `|S_R|` and `h` orbits on `L`, `R` and `M`;
4. the sets `S_L`, `S_R`, the gadget `C`, and the neighbours of a vertex of `Z₀` (in either
   direction) are computable in time polynomial in `m`, by fixed machines working on the
   normal-form codes of `G_m`. -/
theorem theorem_5_1 (t : ℕ) (ht : 1 ≤ t) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∃ (k : ℕ) (PL PR : Fin (2 ^ k) → ℕ) (DR : ℕ) (c : ℝ) (m₀ : ℕ),
      1 ≤ k ∧ Function.Injective (Sum.elim PL PR) ∧
      (∀ i, (PL i).Prime ∧ PL i % 8 = 1) ∧ (∀ i, (PR i).Prime ∧ PR i % 8 = 1) ∧
      d < DR ∧ 0 < c ∧ 3 ≤ m₀ ∧
      2 * Real.sqrt (((∏ i, PL i) * (∏ i, PR i) : ℕ) : ℝ) < 2 ^ m₀ ∧
      ∃ (sL : ∀ m, Fin (t * DR) → Sig ↥(Gm m) (2 ^ k)) (sR : ∀ m, Fin DR → Sig ↥(Gm m) (2 ^ k))
        (gad : ℕ → Fin (t * DR) → Fin DR → Prop),
        (∀ m, m₀ ≤ m →
          Function.Injective (sL m) ∧ Function.Injective (sR m) ∧
          (∀ σ, IsSignature (fun i => AredG m (PL i)) (sL m σ)) ∧
          (∀ τ, IsSignature (fun i => AredG m (PR i)) (sR m τ)) ∧
          IsBiregular (gad m) d (t * d) ∧
          IsSimpleLP (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
            (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ))
            (constGadget (adjMatrix (gad m))) ∧
          IsTwoSidedLossless
            (lpAdj (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
              (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ))
              (constGadget (adjMatrix (gad m))))
            (2 ^ k * d) (2 ^ k * (t * d)) c ε ∧
          DistinctWitness (k := k) (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
            (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ)) ∧
          IsFreeAction ↥(Gm m) (Cell ↥(Gm m) (Fin (t * DR))) ∧
          IsFreeAction ↥(Gm m) (Cell ↥(Gm m) (Fin DR)) ∧
          IsFreeAction ↥(Gm m) (Cell ↥(Gm m) ↥(hadamard k)) ∧
          IsInvariantRel ↥(Gm m)
            (lpAdj (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
              (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ))
              (constGadget (adjMatrix (gad m)))) ∧
          Nat.card (orbitRel.Quotient ↥(Gm m) (Cell ↥(Gm m) (Fin (t * DR)))) = t * DR ∧
          Nat.card (orbitRel.Quotient ↥(Gm m) (Cell ↥(Gm m) (Fin DR))) = DR ∧
          Nat.card (orbitRel.Quotient ↥(Gm m) (Cell ↥(Gm m) ↥(hadamard k))) = 2 ^ k) ∧
        PolyTimeData (fun m => (List.finRange (t * DR)).flatMap fun σ => sigCode m (2 ^ k) (sL m σ))
          m₀ ∧
        PolyTimeData (fun m => (List.finRange DR).flatMap fun τ => sigCode m (2 ^ k) (sR m τ)) m₀ ∧
        PolyTimeData (fun m => gadgetCode (gad m)) m₀ ∧
        (∃ f, PolyTimeFn f ∧
          EnumeratesNbrs (fun m (v : Cell ↥(Gm m) (Fin (t * DR))) => gmCellCode m v)
            (fun m (v : Cell ↥(Gm m) (Fin DR)) => gmCellCode m v)
            (fun m => lpAdj (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
              (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ))
              (constGadget (adjMatrix (gad m)))) m₀ f) ∧
        (∃ f, PolyTimeFn f ∧
          EnumeratesNbrs (fun m (v : Cell ↥(Gm m) (Fin DR)) => gmCellCode m v)
            (fun m (v : Cell ↥(Gm m) (Fin (t * DR))) => gmCellCode m v)
            (fun m r ℓ => lpAdj (fun σ => normCube (fun i => AredG m (PL i)) (sL m σ))
              (fun τ => normCube (fun i => AredG m (PR i)) (sR m τ))
              (constGadget (adjMatrix (gad m))) ℓ r) m₀ f) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
