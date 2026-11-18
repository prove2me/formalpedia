-- Prove2me | Theorems.Thm_HILL_PRG_batch_calls_polytime
-- name    : HILL.PRG.batch_calls_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T02:20:03.929193+00:00
-- url     : https://prove2.me/theorems/f5512d7b-05ca-45ef-8fbb-929b459e608e
-- title:
--   Polynomial-time batch evaluation of encoded words
-- statement:
--   Let $M$ be a polynomial-time transformer on bit strings in the HILL model. Encode each input word by replacing a data bit $b$ with the pair $1b$ and ending the word with a single zero. Concatenate the resulting word encodings. The input to the batch evaluator consists of the HILL unary security and advice fields followed by that list of encoded words.
--
--   There is a single polynomial-time transformer that, for every security parameter, advice value, and finite list of words, calls $M$ on each word with those same unary fields and returns the list of encoded outputs in order. The framing distinguishes word boundaries even for empty words. This supplies the repeated subroutine calls used in formalizing the independent repetitions in HILL Construction 4.15.
-- source:
--   Supporting machine closure lemma for Construction 4.15 and Lemma 4.16 in Håstad, Impagliazzo, Levin, and Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, §4.7. https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf

import Definitions.Def_HILL_PRG_Model
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.Tactic.DeriveFintype

open HILL.PRG

namespace HILL.PRG

theorem batch_calls_polytime (M : Bits → Bits) (hM : PolyTimeComputable M) :
    let quoteBits := fun (w : Bits) => w.flatMap (fun b => [true, b])
    let encodeWords := fun (ws : List Bits) => ws.flatMap (fun w => quoteBits w ++ [false])
    ∃ B : Bits → Bits, PolyTimeComputable B ∧
      ∀ (n a : ℕ) (xs : List Bits),
        B (encAdvice n a (encodeWords xs)) =
          encodeWords (xs.map (fun x => M (encAdvice n a x))) := by sorry

end HILL.PRG
