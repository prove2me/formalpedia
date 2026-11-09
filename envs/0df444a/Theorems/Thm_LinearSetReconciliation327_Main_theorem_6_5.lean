-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_theorem_6_5
-- name    : LinearSetReconciliation327.Main.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:54.218912+00:00
-- url     : https://prove2.me/theorems/1f56ba89-589d-447e-9b32-1692b6453d66
-- title:
--   Theorem 6.5 — Linear set reconciliation with O(d) additive redundancy
-- statement:
--   There are one fixed toggle program and one fixed decoder and absolute constants and exponents such that for all $2\le d\le n$ and $0<\varepsilon\le1/2$, with $\lambda=\lceil\log(1/\varepsilon)\rceil$, there is a public-coin binary linear sketch $H_r:\mathbb F_2^n\to\mathbb F_2^M$, chosen before the input, with $M\le L(n,d)+C_ld+C_l\lambda\log^{p_l}n$; column weight and toggle time at most $C_u\log^{p_u}n$ on every seed, the toggle XORing the actual column into the stored payload; decoding time at most $C_dd\exp(C_d(\log\log n)^2)$ on every seed and every stored payload, including failures; and for each fixed $x\in S_{n,d}$, with probability at least $1-\varepsilon$ over the seed, the decoder outputs the explicit support of $x$. The clause $dn^{o(1)}$ is a consequence of the explicit bound.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - reading: word-RAM with Θ(log n)-bit words, O(1) access to public permutations and inverses, coefficients and precomputed expander tables, preprocessing excluded → one fixed program on a concrete instruction set, width W with clog n ≤ W ≤ cW·log n, uniform permutation and coefficient tables of a TableSpec, and one deterministic seed-independent table of word-address size; reason: §2.1 names the expander adjacency and §§4.2, 5.3, 6.2 precompute parameter-only capacities under the preprocessing exclusion; a fixed program chosen first and a seed-independent table of at most 2^W words exclude free decoders and input or seed advice
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - reading: worst-case decoding takes d exp(O((log log n)²)) time → all seeds and all stored payloads, not only syndromes of sparse inputs; reason: the never-weaker reading of worst case; §5.4 and §6.3 keep the bound on failures and the source procedures are total
--   - encoding: time d n^{o(1)} → omitted as a separate clause; reason: it follows from the explicit bound and adds nothing
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 6.5, identical to Theorem 1.1, PDF p.31–32 (printed p.30–31)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Theorem 6.5 (Main guarantee), PDF p.31 (printed p.30), identical to Theorem 1.1. One toggle
program and one decoder, and absolute constants and exponents, precede `n`, `d`, `ε`, the seed and the
input. The tables, syndrome and maps are selected before the input. Decoding time is worst-case: it
holds for every seed and every stored vector, and the output is an explicit sparse list. -/
theorem theorem_6_5 :
    ∃ (progUp progDec : Program) (cW Cl Cu Cd : ℝ) (pl pu : ℕ),
      0 < cW ∧ 0 ≤ Cl ∧ 0 < Cu ∧ 0 < Cd ∧
      ∀ (n d : ℕ) (ε : ℝ), 2 ≤ d → d ≤ n → 0 < ε → ε ≤ 1 / 2 →
        let lam : ℕ := ⌈lg (1 / ε)⌉₊
        ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
          (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
          WidthOK W n cW (lg n) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
          (M : ℝ) ≤ L n d + Cl * d + Cl * (lam : ℝ) * lg n ^ pl ∧
          (∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)) ∧
          (∀ r, TogglesWithin progUp (spec.env W det r) (H r) (Cu * lg n ^ pu)) ∧
          (∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
            HaltsWithin progDec (spec.env W det r)
              (Cd * (d : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W y []) s') ∧
          (∀ x : Fin n → ZMod 2, (univ.filter fun i => x i = 1).card ≤ d →
            1 - ε ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
              HaltsWithin progDec (spec.env W det r)
                (Cd * (d : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W (H r x) []) s' ∧
              OutputsSupport s' x)) := by sorry

end LinearSetReconciliation327.Main
