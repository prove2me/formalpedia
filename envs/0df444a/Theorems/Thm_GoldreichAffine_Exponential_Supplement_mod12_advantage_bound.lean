-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_mod12_advantage_bound
-- name    : GoldreichAffine.Exponential.Supplement.mod12_advantage_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:29.679885+00:00
-- url     : https://prove2.me/theorems/4ca682c6-004e-4d9c-af86-567af11acb8e
-- title:
--   Theorem 6 — explicit bound $\operatorname{adv}_{b'}(\mathsf{MOD12}_b)\le\min\{1/2,B_{12}(b')\}$
-- statement:
--   For integers $b\ge1$ and $1\le b'\le b$, let
--
--   $$B_{12}(b')=\frac{\sqrt2}{6}\Big[\Big(\cos\frac\pi{12}\Big)^{b'}+\Big(\sin\frac\pi{12}\Big)^{b'}+2^{-b'/2}\Big]+\frac1{\sqrt3}\Big(\frac{\sqrt3}2\Big)^{b'} .$$
--
--   Then the bit-fixing affine advantage of $\mathsf{MOD12}_b$ at $b'$ remaining inputs satisfies
--
--   $$\operatorname{adv}_{b'}(\mathsf{MOD12}_b)\le\min\Big\{\frac12,\ B_{12}(b')\Big\}. \tag{7}$$
--
--   This companion theorem gives an explicit exponentially decaying bound, uniform over all partial input fixings, on how well any residual of MOD12 is approximated by an affine function.
--
--   Differences from the source:
--   - encoding: b ≥ 1 and 1 ≤ b′ ≤ b → 1 ≤ b′ and b′ ≤ b; reason: b ≥ 1 follows from 1 ≤ b′ ≤ b
--   - encoding: 2^{−b′/2} → (2:ℝ) ^ (−(b′:ℝ)/2), a real power; reason: b′ may be odd
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, pp. 10–11 (PDF pp. 11–12), Theorem 6, Eq. (7); proof App. B.2, pp. 29–30 (PDF pp. 30–31)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 6, printed pp.10–11 / PDF pp.11–12, Eq. (7): adv_{b'}(MOD12_b) ≤ min{1/2, B12(b')},
    1 ≤ b' ≤ b (so b ≥ 1). -/
theorem mod12_advantage_bound (b b' : ℕ) (hb' : 1 ≤ b') (hbb : b' ≤ b) :
    advantage (mod12 b) b' ≤ min (1 / 2) (B12 b') := by sorry

end GoldreichAffine.Exponential.Supplement
