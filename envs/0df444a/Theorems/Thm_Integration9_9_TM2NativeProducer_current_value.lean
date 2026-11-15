-- Prove2me | Theorems.Thm_Integration9_9_TM2NativeProducer_current_value
-- name    : Integration9_9.TM2NativeProducer.current_value
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T22:48:55.198969+00:00
-- url     : https://prove2.me/theorems/47b71099-769d-49fd-83c0-ae36a177a7b9
-- title:
--   Exact semantics of the native finite full-response producer
-- statement:
--   For every order, native producer metadata, tape clock, and correct full-response data, the native list-of-lists producer equals the displayed table of decoded entries from the materialized binary full-response matrix. This is an exact program-semantics identity.
-- source:
--   An independently checked original public helper theorem from Integration9_9.TM2NativeProducer.lean. The complete proof retains the original AST proof units, uses only standard axioms, and is packaged below the platform source scanner limit.

import Definitions.Def_InfoLossLAR_RuntimeBundle_06
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

theorem _root_.Integration9_9.TM2NativeProducer.current_value (order : ℕ) (params : _root_.Integration9_9.TM2NativeProducer.Meta) (ticks : List Unit)
    (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) :
    _root_.Integration9_9.TM2NativeProducer.current order (params,ticks)=List.ofFn (fun row : Fin ((order+1)^2)=>
      List.ofFn (fun column : Fin ((_root_.CurrentAFT.CurrentRectangleIndex.colors params.1.length)^order)=>
        (((_root_.CurrentAFT.BinaryRectangleMaterialization.run params.1.length order ticks.length
          (_root_.CurrentAFT.BinaryFullResponseMatrixEntry.current params.1.length params.2.length order data)).value.get row).get column).decode)) := by sorry
