-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_lemma_6
-- name    : MLRPCake.EnvyFree.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:06:50.600263+00:00
-- url     : https://prove2.me/theorems/52cf0c40-2cf0-4734-a01e-da42911af437
-- title:
--   Lemma 6 — strictly before the switching point f_j < f_i, strictly after it f_j ≥ f_i
-- statement:
--   Let $f_i,f_j$ be value densities on $[0,1]$ (nonnegative, Riemann integrable, $\int_0^1 f_i=\int_0^1 f_j=1$, strictly positive on $[0,1]$) that satisfy MLRP: $f_j/f_i$ is nondecreasing on $[0,1]$. Let $p_{ij}=\inf\{x\in[0,1]: f_j(x)\ge f_i(x)\}$ be their switching point. Then
--
--   (a) for all $y\in[0,p_{ij})$,
--   $$\frac{f_j(y)}{f_i(y)}<1;$$
--
--   (b) for all $z\in(p_{ij},1]$,
--   $$\frac{f_j(z)}{f_i(z)}\ge 1.$$
--
--   Nothing is asserted at $p_{ij}$ itself; the densities need not be continuous, so $f_i(p_{ij})=f_j(p_{ij})$ may fail. This single-crossing property underlies the localization of switching points (Corollary 1) and the reduction of the social-welfare problem to the grid $P$ (Lemma 7).
--
--   **Formalization Note** Riemann integrability is encoded, as in the published model, by boundedness together with interval integrability on $[0,1]$.
--
--   Differences from the source:
--   - encoding: two value densities satisfying MLRP (standing positivity and normalization, §2) → functions with the published IsDensity, strict positivity on [0,1], and f_j/f_i nondecreasing on [0,1]; reason: these are the paper's standing hypotheses on value densities; same instances
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 18, Lemma 6

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

namespace MLRPCake.EnvyFree.Supplement

/-- Lemma 6, p. 18: for two value densities bearing MLRP (strictly positive on `[0,1]`, `f_j/f_i`
nondecreasing on `[0,1]`) with switching point `p_{ij} = inf {x ∈ [0,1] : f_j(x) ≥ f_i(x)}`:
(a) `f_j(y)/f_i(y) < 1` for all `y ∈ [0, p_{ij})`, and (b) `f_j(z)/f_i(z) ≥ 1` for all
`z ∈ (p_{ij}, 1]`. -/
theorem lemma_6 (fi fj : ℝ → ℝ) (hi : IsDensity fi) (hj : IsDensity fj)
    (hpos_i : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fi x) (hpos_j : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fj x)
    (hmlrp : ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ 1 → fj b / fi b ≤ fj c / fi c) :
    (∀ y : ℝ, 0 ≤ y → y < switchPt fi fj → fj y / fi y < 1) ∧
    (∀ z : ℝ, switchPt fi fj < z → z ≤ 1 → 1 ≤ fj z / fi z) := by sorry

end MLRPCake.EnvyFree.Supplement
