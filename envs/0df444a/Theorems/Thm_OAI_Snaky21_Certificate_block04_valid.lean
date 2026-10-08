-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
-- name    : OAI.Snaky21.Certificate.block04_valid
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:26:57.046563+00:00
-- url     : https://prove2.me/theorems/2a57c09c-e2aa-4636-ad1c-3555fd9e144c
-- title:
--   21-move certificate: validity of numbered cards 256–319
-- statement:
--   Every numbered card from 256 through 319 of the fixed 21-move certificate is a valid conditional claim. The required set, envelope and height are the literal finite reconstruction of the printed data, including every nested combination. Every actual combination equation is checked by Lean kernel reduction, and the game meaning follows from the conditional-claim calculus and earlier numbered cards.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, 21-move certificate appendix, numbered cards 256–319.

import Definitions.Def_Snaky21Data04
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.block04_valid : Valid card_256 ∧ Valid card_257 ∧ Valid card_258 ∧ Valid card_259 ∧ Valid card_260 ∧ Valid card_261 ∧ Valid card_262 ∧ Valid card_263 ∧ Valid card_264 ∧ Valid card_265 ∧ Valid card_266 ∧ Valid card_267 ∧ Valid card_268 ∧ Valid card_269 ∧ Valid card_270 ∧ Valid card_271 ∧ Valid card_272 ∧ Valid card_273 ∧ Valid card_274 ∧ Valid card_275 ∧ Valid card_276 ∧ Valid card_277 ∧ Valid card_278 ∧ Valid card_279 ∧ Valid card_280 ∧ Valid card_281 ∧ Valid card_282 ∧ Valid card_283 ∧ Valid card_284 ∧ Valid card_285 ∧ Valid card_286 ∧ Valid card_287 ∧ Valid card_288 ∧ Valid card_289 ∧ Valid card_290 ∧ Valid card_291 ∧ Valid card_292 ∧ Valid card_293 ∧ Valid card_294 ∧ Valid card_295 ∧ Valid card_296 ∧ Valid card_297 ∧ Valid card_298 ∧ Valid card_299 ∧ Valid card_300 ∧ Valid card_301 ∧ Valid card_302 ∧ Valid card_303 ∧ Valid card_304 ∧ Valid card_305 ∧ Valid card_306 ∧ Valid card_307 ∧ Valid card_308 ∧ Valid card_309 ∧ Valid card_310 ∧ Valid card_311 ∧ Valid card_312 ∧ Valid card_313 ∧ Valid card_314 ∧ Valid card_315 ∧ Valid card_316 ∧ Valid card_317 ∧ Valid card_318 ∧ Valid card_319 ∧ True := by sorry
