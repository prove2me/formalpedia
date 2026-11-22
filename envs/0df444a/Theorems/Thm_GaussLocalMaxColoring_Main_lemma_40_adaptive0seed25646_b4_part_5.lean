-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_5
-- name    : GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_5
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T14:27:37.385814+00:00
-- url     : https://prove2.me/theorems/1d7225eb-e2db-4386-8ada-565662f5b9a6
-- title:
--   Lemma40 constructive region Adaptive0Seed25646: neighbor interval bound part 5
-- statement:
--   Exact supporting inequality for Lemma40, with the displayed closed rational controls and constructive radical witnesses on the displayed closed A/rho rectangle. For every neighbor correlation r in the displayed closed interval, the original public l40Lhs is at least fA(A,r)+3/10^6. No numerical certificate validity or Taylor estimate is assumed.
-- source:
--   New exact supporting derivation for Lemma40 and AppendixC of the pinned STOC2027 paper155, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/155.pdf, SHA256 9917b0a118555de058fe15a67d4540cda7e2214a8968b4c5dbf0e01f93e65b4b. The original statement and margins are unchanged; the witness parameterization is an alternative constructive proof.

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Section5

open GaussLocalMaxColoring.Main

theorem GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_5 (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(227/1024:ℝ)) ≤ r) (hrhi : r ≤ (-(279/1280:ℝ))) :
    let bv : ℝ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
    let cv : ℝ := (148022665013912365111/4722366482869645213696:ℚ)
    let θv : ℝ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
    let Lv : ℝ := fA A ρ/Real.sqrt (1-ρ^2)
    let Jv : ℝ := Da+1+1/4
    let κv : ℝ := Real.sqrt (1/4-cv^2-1/10^20)
    let Mv : ℝ := Real.sqrt (Jv-Lv^2+1/10^18)
    let μv : ℝ := (Mv-θv*κv)/(1+θv)
    let av : ℝ := Real.sqrt (1-1/10^12-bv^2-μv^2)
    fA A r+3/10^6 ≤ l40Lhs A ρ Lv av bv cv θv r := by sorry
