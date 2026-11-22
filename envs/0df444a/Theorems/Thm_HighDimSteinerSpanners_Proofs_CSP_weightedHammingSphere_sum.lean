-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_weightedHammingSphere_sum
-- name    : HighDimSteinerSpanners.Proofs.CSP.weightedHammingSphere_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:18.038544+00:00
-- url     : https://prove2.me/theorems/597352a0-2aca-4c53-a39b-05f44e18290b
-- title:
--   CSP: weighted Hamming Sphere sum
-- statement:
--   Joint retention weights on an ordered Hamming sphere factor into the expected
--   vertex count and weighted neighbor count. The subtraction guard permits arbitrary radii.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L312-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L312-L339

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.weightedHammingSphere_sum {N q : ℕ} (s : ℕ)
    (hsub : s.choose 2 ≤ s * (N - 1))
    (edgeWeight keepWeight expectedVertices neighborWeight : ℝ)
    (hneighbor : neighborWeight = (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
      edgeWeight ^ (s * (N - 1) - s.choose 2))
    (hvertices : expectedVertices = keepWeight * (q : ℝ) ^ N * edgeWeight ^ N.choose 2)
    (hqueries : ∀ x y : Fin N → Fin q, (homQueries x ∪ homQueries y).card =
      N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2) :
    ∑ xy ∈ Finset.univ.filter (fun xy : (Fin N → Fin q) × (Fin N → Fin q) =>
      dHam xy.1 xy.2 = s),
      keepWeight ^ 2 * edgeWeight ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        expectedVertices * keepWeight * neighborWeight := by sorry
