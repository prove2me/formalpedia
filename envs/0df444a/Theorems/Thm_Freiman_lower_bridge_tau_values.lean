-- Prove2me | Theorems.Thm_Freiman_lower_bridge_tau_values
-- name    : Freiman.lower_bridge_tau_values
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:04:08.013785+00:00
-- url     : https://prove2.me/theorems/82cfe707-2965-448d-b99a-c8e405a234fc
-- title:
--   Exact quadratic values of the A-zero bridge endpoint tails
-- statement:
--   Let $\tau=\sqrt{3}-1$, and for a finite word $w=(d_1,\ldots,d_m)$ let $F_w(\tau)$ denote the continued-fraction prefix applied to the tail $\tau$ defined recursively by $F_{()}(t)=t$ and $F_{(d,w)}(t)=1/(d+F_w(t))$.
--
--   For each of the34 endpoint words occurring in the A-zero bridge comparisons and the five referenced endpoint constants, the displayed rational coefficients satisfy
--
--   $$F_w(\tau)=a_w+b_w\sqrt{3}.$$
--
--   The formal statement records the complete table of exact rational coefficients. These equalities provide a reusable finite certificate for evaluating the bridge endpoint differences and their matrix numerators. All source words and coefficient pairs are explicit; no bridge inequality is assumed.
-- source:
--   Exact endpoint continued fractions from Freiman’s Hall ray report (8 September 2026), initial_bridges.tex and H_entry_bridges.json, the aZero bridge records and lowerTheta entries3,25,36,63,66. The fixed source words are given in the public Definitions Freiman_lowerBridgeData_aZero and Freiman_lowerSelection; this certificate evaluates their endpoint tails exactly from the published prefixEval recursion and lowerTau = sqrt(3)-1.

import Definitions.Def_Freiman_lowerSelection
open Freiman

theorem Freiman.lower_bridge_tau_values :
  (prefixEval [] lowerTau = (-1 : ℝ) + 1 * Real.sqrt 3) ∧
  (prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [2,3] lowerTau = (4 / 13 : ℝ) + (1 / 13 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [3,3] lowerTau = (5 / 22 : ℝ) + (1 / 22 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,1,3] lowerTau = (9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3] lowerTau = (355 / 481 : ℝ) + (-1 / 481 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3] lowerTau = (735 / 1006 : ℝ) + (1 / 1006 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,2,3] lowerTau = (2513 / 3421 : ℝ) + (1 / 3421 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3] lowerTau = (4087 / 5566 : ℝ) + (1 / 5566 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,1,3] lowerTau = (1006 / 1367 : ℝ) + (-1 / 4101 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,2,1,3] lowerTau = (2504 / 3407 : ℝ) + (-1 / 10221 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,2,3] lowerTau = (27413 / 37318 : ℝ) + (-1 / 37318 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,2,1,3] lowerTau = (17117 / 23257 : ℝ) + (1 / 23257 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,1,1,3] lowerTau = (33633 / 45793 : ℝ) + (1 / 45793 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,2,1,3] lowerTau = (82443 / 112237 : ℝ) + (1 / 112237 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,2,3] lowerTau = (299030 / 407077 : ℝ) + (1 / 407077 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,3] lowerTau = (484195 / 659149 : ℝ) + (1 / 659149 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,1,2,1,3] lowerTau = (190985 / 260038 : ℝ) + (-1 / 260038 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,1,1,3] lowerTau = (122055 / 166154 : ℝ) + (-1 / 498462 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,2,1,3] lowerTau = (299605 / 407858 : ℝ) + (-1 / 1223574 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,2,3] lowerTau = (3261917 / 4440529 : ℝ) + (-1 / 4440529 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3,1,3,2,3] lowerTau = (804501 / 1098526 : ℝ) + (1 / 1098526 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,3] lowerTau = (253237 / 343967 : ℝ) + (1 / 1031901 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,1,2,1,3] lowerTau = (2079038 / 2830201 : ℝ) + (1 / 2830201 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,1,1,3] lowerTau = (3994962 / 5438449 : ℝ) + (1 / 5438449 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,2,1,3] lowerTau = (9805068 / 13347889 : ℝ) + (1 / 13347889 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,2,1,3,1,3,2,1,3] lowerTau = (2402518 / 3280573 : ℝ) + (-1 / 3280573 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,1,3] lowerTau = (2304533 / 3130198 : ℝ) + (-1 / 3130198 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,2,3] lowerTau = (4377673 / 5946097 : ℝ) + (-1 / 5946097 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,3,3,3,1,2,1,3] lowerTau = (22683113 / 30879133 : ℝ) + (-1 / 30879133 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,1,1,3] lowerTau = (5735298 / 7790137 : ℝ) + (1 / 7790137 : ℝ) * Real.sqrt 3) ∧
  (prefixEval [1,2,1,3,1,3,1,2,2,2,1,3] lowerTau = (13419276 / 18227113 : ℝ) + (1 / 18227113 : ℝ) * Real.sqrt 3) := by
  sorry
