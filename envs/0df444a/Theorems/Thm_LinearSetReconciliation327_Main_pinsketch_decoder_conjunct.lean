-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_conjunct
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_conjunct
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:45:37.039122+00:00
-- url     : https://prove2.me/theorems/19a605b0-c846-4193-a4dc-b4ba791dce80
-- title:
--   Pinsketch decoder: the decoding conjunct of Proposition 2.1
-- statement:
--   This is the third conjunct of Proposition 2.1: the explicit decoder exists and is polynomial-time.
--
--   For every $N \ge 1$, every $t \le N$, every field $F$ of characteristic two, every $w$ with $N < 2^{w}$ and every basis $b$ of $F$ over $\mathbb{Z}_2$ with $w$ coordinates, and every injective sequence $(\iota_0,\dots,\iota_{N-1})$ of nonzero elements of $F$, there are a word width $W$ and a field-data table `det` such that:
--   1. `WidthOK W N 8 w` holds and $t w$ words fit in $2^{W}$ memory cells;
--   2. for every packed syndrome $y \in (\mathbb{Z}_2^{w})^{t}$, the word-RAM program `pinsketchDecoderProgram`, started from `decoderStart W y []`, halts within
--
--   $$
--   20000\,\bigl(t+w+1\bigr)^{6}
--   $$
--
--   steps in a state satisfying `decoderPost`, i.e. it outputs a $t$-light vector with syndrome $y$ when one exists, and rejects only when none exists.
--
--   This is the whole decoder guarantee of Proposition 2.1, obtained by composing the four stage contracts (read, key solver, root search, verifier) and the glue lemmas that sequence them. It is the node any later result about the Pinsketch decoder can cite.
--
--   **Formalization Note** `pinsketchDecoderProgram` is a concrete `Program` (a published definition), not an existentially quantified object; `WidthOK` and `wordsOf` are the word-RAM width/space predicates, and the time bound is the paper's $O((t+w+1)^{6})$ with the explicit constant $20000$.
-- source:
--   arXiv:2611.11409, Section 2.2, Proposition 2.1 (decoding conjunct), and Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_root_search
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_verifier

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_conjunct
    {F : Type} [Field F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hN : 1 ≤ N) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) :
    ∃ (W : ℕ) (det : ℕ → ℕ), WidthOK W N 8 (w : ℝ) ∧ wordsOf W (t * w) ≤ 2 ^ W ∧
      ∀ y : Fin (t * w) → ZMod 2, ∃ s',
        HaltsWithin pinsketchDecoderProgram (detEnv W det) (20000 * ((t : ℝ) + w + 1) ^ 6)
          (decoderStart W y []) s' ∧ decoderPost (N := N) b ι y s' := by sorry
