-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_theorem_5_1
-- name    : LinearSetReconciliation327.Main.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:52.47529+00:00
-- url     : https://prove2.me/theorems/2318439b-2821-458e-9b37-d88f627e7540
-- title:
--   Theorem 5.1 — Performance of HintSketch
-- statement:
--   There are one fixed toggle program and one fixed decoder, and absolute constants and exponents including $\alpha$, such that for all $n\ge2$, $\lambda\ge1$ and nodes $1\le N\le n$, $0\le X,Y\le N$ there is a public-coin binary linear sketch, chosen independently of input and hint, with length at most $(1+C_1/\log n)(X+\alpha h_N(Y))+C_2N/\log^8n+C_3\lambda\log^{p_1}n$, column weight and toggle time at most $C_u\log^{p_u}n$, and decoding time at most $C_dN\exp(C_d(\log\log n)^2)$ on every seed, stored vector and hint list. For every fixed input and hint with $|J|\le X$, $|\mathrm{supp}(x)\setminus J|\le Y$, the decoder outputs the explicit support of $x$ except with probability at most $2^{-\lambda}$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - reading: word-RAM with Θ(log n)-bit words, O(1) access to public permutations and inverses, coefficients and precomputed expander tables, preprocessing excluded → one fixed program on a concrete instruction set, width W with clog n ≤ W ≤ cW·log n, uniform permutation and coefficient tables of a TableSpec, and one deterministic seed-independent table of word-address size; reason: §2.1 names the expander adjacency and §§4.2, 5.3, 6.2 precompute parameter-only capacities under the preprocessing exclusion; a fixed program chosen first and a seed-independent table of at most 2^W words exclude free decoders and input or seed advice
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - reading: λ = ⌈log(1/ε)⌉ of §2.1, replaced by λ + ⌈log 2ℓ⌉ in §6.2 → every natural λ ≥ 1; reason: the proof treats λ as a free parameter and §6.2 applies it to values that are not of the form ⌈log(1/ε)⌉ for the outer ε
--   - reading: worst-case decoding time, including when recovery fails → all seeds, all stored vectors, all duplicate-free hint lists in [N]; reason: §5.4 stops CR calls at their time bound so the bound holds whenever recovery fails; the worker bound does not depend on the syndrome or the hint size
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1, PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Theorem 5.1 (Performance of HintSketch), PDF p.19 (printed p.18). Every constant and exponent is
absolute and precedes the node `(N, X, Y)`, `n` and `λ`. -/
theorem theorem_5_1 :
    ∃ (progUp progDec : Program) (cW α C₁ C₂ C₃ Cu Cd : ℝ) (p₁ pu : ℕ),
      0 < cW ∧ 0 ≤ α ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < Cu ∧ 0 < Cd ∧
      ∀ n lam N X Y : ℕ, 2 ≤ n → 1 ≤ lam → 1 ≤ N → N ≤ n → X ≤ N → Y ≤ N →
        ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
          (H : spec.Seed → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
          WidthOK W n cW (lg n) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
          (M : ℝ) ≤ (1 + C₁ / lg n) * ((X : ℝ) + α * hN N Y) + C₂ * ((N : ℝ) / lg n ^ 8) +
            C₃ * (lam : ℝ) * lg n ^ p₁ ∧
          (∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)) ∧
          (∀ r, TogglesWithin progUp (spec.env W det r) (H r) (Cu * lg n ^ pu)) ∧
          -- worst-case time: every seed, every stored vector, every hint list
          (∀ (r : spec.Seed) (y : Fin M → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) →
            ∃ s' : RAMState, HaltsWithin progDec (spec.env W det r)
              (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W y J) s') ∧
          -- the matrices do not depend on the hint; recovery of each fixed input and hint with (3)
          (∀ (x : Fin N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) → J.length ≤ X →
            ((univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).card ≤ Y) →
            prU (fun r : spec.Seed => ¬ ∃ s' : RAMState,
                HaltsWithin progDec (spec.env W det r)
                  (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W (H r x) J) s' ∧
                OutputsSupport s' x) ≤ ((2 : ℝ) ^ lam)⁻¹) := by sorry

end LinearSetReconciliation327.Main
