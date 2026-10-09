-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_36
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_36
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:18:33.869239+00:00
-- url     : https://prove2.me/theorems/2181edb8-1415-4b70-83a9-caf1a5a1506e
-- title:
--   Sidorenko construction: Coefficients, batch 36
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Coefficients.lean; source propositions faceSide_correct, faceSlot_side, faceSide_slot, pairCorner_image_0, pairCorner_image_1, pairCorner_image_2, pairCorner_image_3, pairCorner_image_4, pairCorner_image_5, pairCorner_image_6, pairCorner_image_7, pairCorner_image_8, pairCorner_image_9, pairCorner_image_10, pairCorner_image_11, pairCorner_image_12, pairCorner_image_13, pairCorner_image_14, pairCorner_image_15, pairCorner_image_16, pairCorner_image_17, pairCorner_image_18, pairCorner_image_19, pairCorner_image_20, pairCorner_image_21, pairCorner_image_22, pairCorner_image_23, pairCorner_image_24, pairCorner_image_25, pairCorner_image_26, pairCorner_image_27, pairCorner_image_28, pairCorner_image_29, pairCorner_image_30, pairCorner_image_31, pairCorner_image_32, pairCorner_image, pairCorner_inj, pairCorners_product, FiniteLaw.mean_expansion_product, uniformMean_double_product, activationMoment_product, mean_activation_expansion, labels_incidence_product, expandedModel_expansion, expandedModel_mean, coordinateSigns_good, coordinateSigns_real, coordinate_factor, coordinate_boolean_product, coordinateModel_eq, coordinateModels_product, uniformMean_coordinate_factor, uniformMean_law_swap, independent_mean_equiv, independent_mean_prod, faceVertex_mem, faceVertex_surj.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_36
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0377]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0439]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0919]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_1000]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_1006]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_1016]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_1072]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_1073]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_1224]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_1230]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_1232]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_1233]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_1234] :
  OAI.SidorenkoCounterexample.ProofCertificate_1235 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1236 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1237 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1238 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1239 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1240 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1241 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1242 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1243 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1244 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1245 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1246 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1247 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1248 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1249 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1250 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1251 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1252 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1253 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1254 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1255 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1256 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1257 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1258 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1259 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1260 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1261 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1262 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1263 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1264 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1265 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1266 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1267 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1268 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1269 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1270 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1271 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1272 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1273 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1274 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1275 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1276 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1277 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1278 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1279 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1280 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1281 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1282 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1283 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1284 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1285 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1286 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1287 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1288 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1289 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1290 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1291 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1292 := by sorry
