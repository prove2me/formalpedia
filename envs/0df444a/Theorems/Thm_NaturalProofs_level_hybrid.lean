-- Prove2me | Theorems.Thm_NaturalProofs_level_hybrid
-- name    : NaturalProofs.level_hybrid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:32.22951+00:00
-- url     : https://prove2.me/theorems/88c1f1f1-3713-4eea-908e-ff91f4055d87
-- title:
--   Natural Proofs: level hybrid
-- statement:
--   The hybrid argument over the levels of the tree. A test `T` of truth tables that tells the
--   functions `prf G k n s` (random seed `s`) apart from random functions with advantage `δ` tells
--   apart, for some depth `i < n` and some fixed labels, one output of `G k` from a uniform string
--   with advantage at least `δ / (n 2 ^ i)`.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L125-L169
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L125-L169

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)

theorem NaturalProofs.level_hybrid {k : ℕ} (hk : 0 < k) (n : ℕ) (hn : 0 < n) (T : BoolFn n → Bool) :
    ∃ i < n, ∃ (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool),
      |prob (fun s => T (prf G k n s)) - prob T| / (n * 2 ^ i) ≤
        |prob (fun u : Bits k => T (hybF G (i + 1) (expand (Function.update c e (G k u))))) -
          prob (fun y : Fin (2 * k) → Bool => T (hybF G (i + 1) (expand (Function.update c e y))))| := by sorry
