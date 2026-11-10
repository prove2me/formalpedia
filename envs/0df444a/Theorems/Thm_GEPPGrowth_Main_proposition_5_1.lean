-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_5_1
-- name    : GEPPGrowth.Main.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:54.147381+00:00
-- url     : https://prove2.me/theorems/a081ca5d-1549-4fba-a8e9-a659ad95dd61
-- title:
--   Proposition 5.1 — Isotropic growth cone probability
-- statement:
--   Fix $d\ge4$. Let $v\in\mathbb R^d$ be a unit vector. Define $E\subseteq\mathbb R^d$ as
--
--   $$
--   E:=\left\{y\in\mathbb R^d\;\middle|\;v[i]^2\ge\dfrac1d,\ \|r\|_2^2\ge\dfrac d2,\text{ and }v[i]\langle v[-i],r[-i]\rangle\le0,\right.
--   $$
--   $$
--   \left.\text{where }i:=\arg\max_{1\le j\le d}|y[j]|,\ r:=\dfrac{y}{y[i]}\right\}
--   $$.
--
--   Then,
--
--   $$
--   \Pr_{y\sim N(0,I_d)}(y\in E)\ge\dfrac{0.16^d}{2d}
--   $$.
--
--   This gives the isotropic probability of the full growth cone.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: a maximizing pivot with arbitrary ties → an arbitrary maximizing selector, with outer probability and no measurability hypothesis on that selector; reason: retains every tie resolution; the source positive definite Gaussian laws give zero mass to tie columns
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 5.1, printed p.16, PDF p.17

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 5.1, printed p.16 / PDF p.17. Every maximizing selector and every unit v; all three cone conditions. Gaussian ties have measure zero. -/
theorem proposition_5_1 (d : ℕ) (hd : 3 ≤ d) (v : Vec (d+1)) (hv : sqLength v = 1)
    (p : Vec (d+1) → Fin (d+1))
    (hmax : ∀ y, IsMaxPivot y (p y)) :
    (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)) ≤
      prob (normal (1 : Mat (d+1))) (growthConeWith p v) := by sorry

end GEPPGrowth.Main
