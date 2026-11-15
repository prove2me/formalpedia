-- Prove2me | Theorems.Thm_Integration9_9_GaussianRankOnePre_current_value_clipped
-- name    : Integration9_9.GaussianRankOnePre.current_value_clipped
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T00:35:22.591516+00:00
-- url     : https://prove2.me/theorems/d0e849d6-f7bc-45b7-85c5-387ea2d6ddc2
-- title:
--   Exact tape-split semantics of the combined Gaussian rank-one preprocessor
-- statement:
--   For every fixed order, correct binary full-response data, polynomial public-bit bound, positive block count, and Boolean tape long enough for the displayed affine and rank-one coin budgets, the concrete combined Gaussian/rank-one preprocessor has the exact output word shown in the formal statement. It applies the fixed-family actual affine sampler independently to every input block using the initial block-indexed tape segment, serializes the transformed table, and feeds the remaining canonical tape segment to the bounded rank-one preprocessor. The identity holds pointwise for every input table and every complete tape.
-- source:
--   Original public theorem Integration9_9.GaussianRankOnePre.current_value_clipped in Solutions.AdvantageBridgeCombinedProbability, lines 112–134. Original source SHA256 5fdae99e82f78a7a6dd4d3924d37489faa27c2a7478ab864be887d30bf323b17. Metadata type independently exported from the original proved library and compared byte-for-byte with the submitted header; complete extracted proof checked under standard axioms.

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_09
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 65536

theorem _root_.Integration9_9.GaussianRankOnePre.current_value_clipped :
∀ (order : ℕ) (data : CurrentAFT.BinaryFullResponseData.Data order),
  CurrentAFT.BinaryFullResponseData.Correct data →
    ∀ (m : Polynomial ℕ)
      (hbits : ∀ (security : ℕ), (CurrentAFT.PublicBitTapes.current security).bits ≤ Polynomial.eval security m)
      (fallback : QAlgorithms.Complexity.Str) (security count total : ℕ),
      0 < count →
        ∀
          (h :
            count * Polynomial.eval security m +
                (InfoLossLAR.WorstCase.famq security ^ (InfoLossLAR.WorstCase.famN security + count)).size ≤
              total)
          (tape : Fin total → Bool)
          (table :
            Fin count →
              Matrix (Fin (InfoLossLAR.WorstCase.famd security)) (Fin (InfoLossLAR.WorstCase.famN security))
                  (ZMod (InfoLossLAR.WorstCase.famq security)) ×
                (Fin (InfoLossLAR.WorstCase.famd security) → ZMod (InfoLossLAR.WorstCase.famq security))),
          Integration9_9.GaussianRankOnePre.current order m fallback
              (InfoLossLAR.WorstCase.encPair (List.ofFn tape)
                (InfoLossLAR.WorstCase.encInput security (InfoLossLAR.WorstCase.famPP security)
                  (InfoLossLAR.WorstCase.encTable table))) =
            Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
              (InfoLossLAR.WorstCase.encPair
                (List.ofFn fun bit => tape (Fin.castLE h (Fin.natAdd (count * Polynomial.eval security m) bit)))
                (InfoLossLAR.WorstCase.encInput security (InfoLossLAR.WorstCase.famPP security)
                  (InfoLossLAR.WorstCase.encTable
                    (InfoLossLAR.WorstCase.affineObservedTable
                      (InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security)
                      (fun block bit =>
                        tape
                          (Fin.castLE h
                            (Fin.castAdd
                              (InfoLossLAR.WorstCase.famq security ^ (InfoLossLAR.WorstCase.famN security + count)).size
                              (finProdFinEquiv (block, bit)))))
                      table)))) := by sorry
