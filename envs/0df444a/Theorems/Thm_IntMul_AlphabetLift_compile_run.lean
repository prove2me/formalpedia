-- Prove2me | Theorems.Thm_IntMul_AlphabetLift_compile_run
-- name    : IntMul.AlphabetLift.compile_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:57:05.469086+00:00
-- url     : https://prove2.me/theorems/933f99fb-7a2b-49d3-b0c8-17964577b290
-- title:
--   Same-clock alphabet compilation preserving complete multitape runs and exact outputs
-- statement:
--   Every finite multitape machine $M$ admits an alphabet-compatible finite compiler $\widehat M$ with the same tapes, states, head positions, and transition count. The original start symbol maps to the global marker; all other symbols are tagged. For every configuration $c$ and time $t$,
--
--   $$\widehat M^t(\iota(c))=\iota(M^t(c)).$$
--
--   Standard initial $x\#y$ configurations correspond under $\iota$. For every binary output word $w$, $\widehat M$ halts with exact output $w$ at time $t$ if and only if $M$ does so. Thus routines using the original alphabet can participate in controllers over the tagged alphabet of interior work banks without an added clock or a hidden tape-position change.
-- source:
--   Original literal alphabet compiler with complete configuration and exact-output equivalence. Written by Codex.

import Definitions.Def_IntMul_TaggedAlphabetLift
import Mathlib.Tactic

open IntMul IntMul.AlphabetLift

theorem IntMul.AlphabetLift.compile_run (M : MultitapeTM) :
    (∀ c : M.Cfg, ∀ t : ℕ, (machine M).step^[t] (embed M c)=embed M (M.step^[t] c)) ∧
    (∀ x y : List Bool, ∀ t : ℕ,
      (machine M).step^[t] ((machine M).initCfg x y)=embed M (M.step^[t] (M.initCfg x y))) ∧
    (∀ x y w : List Bool, ∀ t : ℕ,
      (machine M).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w) := by sorry
