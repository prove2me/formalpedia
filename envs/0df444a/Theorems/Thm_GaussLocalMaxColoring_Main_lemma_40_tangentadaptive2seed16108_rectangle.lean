-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_tangentadaptive2seed16108_rectangle
-- name    : GaussLocalMaxColoring.Main.lemma_40_tangentadaptive2seed16108_rectangle
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T14:51:05.062368+00:00
-- url     : https://prove2.me/theorems/ce7f991e-c49c-4efc-8395-016b17cf50f1
-- title:
--   Lemma40: constructive Case1 witnesses on a tangent-certified rectangle
-- statement:
--   For every A and rho in the displayed closed rectangle satisfying the original Case1 hypothesis q_A(A,rho)<q_c(rho), there exist all six original Lemma40 Case1 witness parameters, and q_A(A,rho)/sqrt(1-rho²)>0. The conclusion retains every original norm margin and all neighbor-correlation inequalities. A constructive radical witness family and a rigorous tangent bound prove this whole closed real rectangle, containing 1,629 original supplementary rectangles.
-- source:
--   New exact supporting derivation for Lemma40 and AppendixC of the pinned STOC2027 paper155, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/155.pdf, SHA256 9917b0a118555de058fe15a67d4540cda7e2214a8968b4c5dbf0e01f93e65b4b. The original statement and margins are unchanged; the witness parameterization is an alternative constructive proof.

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Section5
open GaussLocalMaxColoring.Main

theorem GaussLocalMaxColoring.Main.lemma_40_tangentadaptive2seed16108_rectangle (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) (hcase : qA A ρ < qc ρ) :
    (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ/Real.sqrt (1-ρ^2) := by sorry
