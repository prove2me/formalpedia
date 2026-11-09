-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_proposition_2_1
-- name    : LinearSetReconciliation327.Main.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:49.555839+00:00
-- url     : https://prove2.me/theorems/761716b6-07ff-4b65-9de0-47c9b7bcb8dc
-- title:
--   Proposition 2.1 — Pinsketch
-- statement:
--   There are one fixed decoding program, constants $K,c_W>0$ and an exponent $p$ such that for all $0\le t\le N$, $N\ge1$, $w=\lceil\log(N+1)\rceil$, every field $F$ of characteristic two with an $\mathbb F_2$-basis of size $w$, and every injection $\iota:[N]\to F^*$: $\mathrm{Pin}_{N,t}$ is $\mathbb F_2$-linear and its syndrome is exactly $tw$ bits; on every $tw$-bit syndrome the deterministic decoder halts within $K(t+w+1)^p$ steps and either reports failure, in which case no $x\in S_{N,t}$ matches, or outputs an explicit support of an $x\in S_{N,t}$ matching the syndrome; a vector of $S_{N,t}$ is determined by its syndrome; a coordinate update is at most $K(t+1)$ field operations and changes at most $tw$ bits; and for $0\le a\le t$ the first $a$ field elements of $\mathrm{Pin}_{N,t}(x)$ are $\mathrm{Pin}_{N,a}(x)$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - reading: word-RAM with Θ(log n)-bit words, O(1) access to public permutations and inverses, coefficients and precomputed expander tables, preprocessing excluded → one fixed program on a concrete instruction set, width W with clog n ≤ W ≤ cW·log n, uniform permutation and coefficient tables of a TableSpec, and one deterministic seed-independent table of word-address size; reason: §2.1 names the expander adjacency and §§4.2, 5.3, 6.2 precompute parameter-only capacities under the preprocessing exclusion; a fixed program chosen first and a seed-independent table of at most 2^W words exclude free decoders and input or seed advice
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - encoding: poly(t,w) → K(t+w+1)^p with absolute K, p; reason: polynomial in t and w, with the sum avoiding a zero bound at t=0
--   - encoding: ⊥ output → register 2 is zero exactly on failure; reason: a concrete report of ⊥
--   - encoding: O(t) field operations → a straight-line program of additions and multiplications of length at most K(t+1), fixed before the inputs; reason: field operations are counted in the abstract field, as the source states them
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Proposition 2.1, PDF p.10 (printed p.9)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Proposition 2.1 (Pinsketch), PDF p.10 (printed p.9). -/
theorem proposition_2_1 :
    ∃ (progDec : Program) (K cW : ℝ) (p : ℕ), 0 < K ∧ 0 < cW ∧
      ∀ (N t : ℕ), 1 ≤ N → t ≤ N →
      ∀ (F : Type) [Field F] [Algebra (ZMod 2) F]
        (w : ℕ) (_hw : w = ⌈lg ((N : ℝ) + 1)⌉₊)
        (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
        (_h0 : ∀ v < N, ι v ≠ 0) (_hinj : Set.InjOn ι (Set.Iio N)),
        -- the map is F₂-linear and uses exactly `tw` bits
        IsLinearMap (ZMod 2) (pin (N := N) ι t) ∧
        Function.Bijective (pinBits (t := t) b) ∧
        -- deterministic, total decoding in time `poly(t, w)`
        (∃ (W : ℕ) (det : ℕ → ℕ), WidthOK W N cW (w : ℝ) ∧ wordsOf W (t * w) ≤ 2 ^ W ∧
          ∀ y : Fin (t * w) → ZMod 2, ∃ s' : RAMState,
            HaltsWithin progDec (detEnv W det) (K * ((t : ℝ) + w + 1) ^ p)
              (decoderStart W y []) s' ∧
            (s'.regs 2 ≠ 0 →
              ∃ x : Fin N → ZMod 2,
                (univ.filter fun i => x i = 1).card ≤ t ∧ pinBits b (pin ι t x) = y ∧
                  OutputsSupport s' x) ∧
            (s'.regs 2 = 0 →
              ¬ ∃ x : Fin N → ZMod 2,
                (univ.filter fun i => x i = 1).card ≤ t ∧ pinBits b (pin ι t x) = y)) ∧
        -- recovery of every `x ∈ S_{N,t}`: a light vector is determined by its syndrome
        (∀ x x' : Fin N → ZMod 2, (univ.filter fun i => x i = 1).card ≤ t →
          (univ.filter fun i => x' i = 1).card ≤ t → pin ι t x = pin ι t x' → x = x') ∧
        -- an update uses `O(t)` field operations and changes at most `tw` bits
        (∃ ops : List (Bool × ℕ × ℕ), (ops.length : ℝ) ≤ K * ((t : ℝ) + 1) ∧
          ∃ out : Fin t → ℕ, ∀ (a : F) (s : Fin t → F) (j : Fin t),
            (slpEval (a :: List.ofFn s) ops).getD (out j) 0 = s j + a ^ (2 * j.val + 1)) ∧
        (∀ (x : Fin N → ZMod 2) (i : Fin N),
          (univ.filter fun p => pinBits b (pin ι t (x + Pi.single i 1)) p ≠
            pinBits b (pin ι t x) p).card ≤ t * w) ∧
        -- every prefix of the syndrome is the shorter syndrome
        (∀ (a : ℕ) (ha : a ≤ t) (x : Fin N → ZMod 2) (j : Fin a),
          pin ι t x (Fin.castLE ha j) = pin ι a x j) := by sorry

end LinearSetReconciliation327.Main
