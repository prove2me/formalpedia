-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_proposition_2_3
-- name    : LinearSetReconciliation327.Main.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:45.615069+00:00
-- url     : https://prove2.me/theorems/10379e5b-4a86-4345-bca9-95c447bef410
-- title:
--   Proposition 2.3 — Deterministic CR sparse recovery
-- statement:
--   There are fixed update and decoding programs and constants $K,c_W>0$ such that for $N\ge1$ and $0\le t\le N$ there is a fixed binary matrix $CR_{N,t}$ with at most $Kt\log^2(N+2)$ rows and column weight at most $K\log^2(N+2)$; a coordinate update of $x$ takes at most $K\log^2(N+2)$ steps, and from $CR_{N,t}x$ the deterministic decoder recovers every $x\in S_{N,t}$ as an explicit support within $K\max\{1,t\log(t+2)\log(N+2)\}$ steps. No random table is used; the expander adjacency lies in the deterministic preprocessed table.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - reading: word-RAM with Θ(log n)-bit words, O(1) access to public permutations and inverses, coefficients and precomputed expander tables, preprocessing excluded → one fixed program on a concrete instruction set, width W with clog n ≤ W ≤ cW·log n, uniform permutation and coefficient tables of a TableSpec, and one deterministic seed-independent table of word-address size; reason: §2.1 names the expander adjacency and §§4.2, 5.3, 6.2 precompute parameter-only capacities under the preprocessing exclusion; a fixed program chosen first and a seed-independent table of at most 2^W words exclude free decoders and input or seed advice
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - encoding: decoder time O(t log(t+2) log(N+2)), which is zero at t=0 → K·max{1, t log(t+2) log(N+2)}; reason: a machine takes at least one step, so this is the same bound with the t=0 convention made explicit
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Proposition 2.3, PDF p.10 (printed p.9)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Proposition 2.3 (Deterministic sparse recovery), PDF p.10 (printed p.9). -/
theorem proposition_2_3 :
    ∃ (progUp progDec : Program) (K cW : ℝ), 0 < K ∧ 0 < cW ∧
      ∀ N t : ℕ, 1 ≤ N → t ≤ N →
        ∃ (W R : ℕ) (det : ℕ → ℕ) (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2)),
          WidthOK W N cW (lg ((N : ℝ) + 2)) ∧ wordsOf W R ≤ 2 ^ W ∧
          (R : ℝ) ≤ K * ((t : ℝ) * lg ((N : ℝ) + 2) ^ 2) ∧
          ColumnWeightLE H (K * lg ((N : ℝ) + 2) ^ 2) ∧
          TogglesWithin progUp (detEnv W det) H (K * lg ((N : ℝ) + 2) ^ 2) ∧
          ∀ x : Fin N → ZMod 2, (univ.filter fun i => x i = 1).card ≤ t →
            ∃ s' : RAMState,
              HaltsWithin progDec (detEnv W det)
                (K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)))
                (decoderStart W (H x) []) s' ∧
              OutputsSupport s' x := by sorry

end LinearSetReconciliation327.Main
