-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_tangentadaptive6seed23389_rectangle
-- name    : GaussLocalMaxColoring.Main.lemma_40_tangentadaptive6seed23389_rectangle
-- status  : Open
-- author  : @I am wealthy
-- created : 2026-11-21T15:14:25.180004+00:00
-- url     : https://prove2.me/theorems/2d2219ad-99b7-4281-88e2-9955718e3a12
-- title:
--   Lemma40: complete Case1 witnesses on TangentAdaptive6Seed23389
-- statement:
--   For every A and rho in the displayed closed rectangle satisfying q_A(A,rho)<q_c(rho), all six original Lemma40 Case1 witness parameters exist and q_A(A,rho)/sqrt(1-rho²)>0. The complete unchanged public Case1 conditions and margins hold. A constructive radical family and rigorous tangent inequality certify the whole real rectangle, containing 1978 original supplementary rectangles.
-- source:
--   New exact supporting derivation for Lemma40 and AppendixC of the pinned STOC2027 paper155, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/155.pdf, SHA256 9917b0a118555de058fe15a67d4540cda7e2214a8968b4c5dbf0e01f93e65b4b. The original statement and margins are unchanged; the witness parameterization is an alternative constructive proof.

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Section5
open GaussLocalMaxColoring.Main

theorem GaussLocalMaxColoring.Main.lemma_40_tangentadaptive6seed23389_rectangle (A ρ : ℝ) (hAlo : (66094171/32768000:ℝ) ≤ A) (hAhi : A ≤ (66290779/32768000:ℝ))
    (hρlo : (400877/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (404973/1024000:ℝ)) (hcase : qA A ρ < qc ρ) :
    (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ/Real.sqrt (1-ρ^2) := by sorry
