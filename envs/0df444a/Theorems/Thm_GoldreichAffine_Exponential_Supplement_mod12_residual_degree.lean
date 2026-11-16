-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_mod12_residual_degree
-- name    : GoldreichAffine.Exponential.Supplement.mod12_residual_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:03.621199+00:00
-- url     : https://prove2.me/theorems/2345faf2-84f9-4d3b-908a-167cdf10fcd3
-- title:
--   Theorem 4 — every $b'$-input residual of MOD12 has degree between $b'-5$ and $b'$
-- statement:
--   Let $b\ge6$ and $6\le b'\le b$. For every residual $M'\in\mathcal R_{b'}(\mathsf{MOD12}_b)$, i.e. every predicate obtained from $\mathsf{MOD12}_b$ by fixing $b-b'$ of its inputs to arbitrary values,
--
--   $$b'-5\le\deg(M')\le b',$$
--
--   and hence $\deg(M')=\Theta(b')$.
--
--   This companion theorem shows that MOD12 keeps algebraic degree linear in the number of free inputs under every partial fixing.
--
--   Differences from the source:
--   - encoding: b ≥ 6 and 6 ≤ b′ ≤ b → 6 ≤ b′ and b′ ≤ b; reason: b ≥ 6 follows from 6 ≤ b′ ≤ b
--   - encoding: deg(M′) = Θ(b′) → the two explicit bounds b′ − 5 ≤ deg M′ ≤ b′; reason: the paper derives Θ(b′) from exactly these bounds ('and hence')
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 10 (PDF p. 11), Theorem 4; proof App. B.3, p. 32 (PDF p. 33)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
import Definitions.Def_GoldreichAffine_Exponential_Supplement_Algebraic
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 4, printed p.10 / PDF p.11: b' - 5 ≤ deg(M') ≤ b' for every M' ∈ R_{b'}(MOD12_b),
    6 ≤ b' ≤ b (so b ≥ 6). -/
theorem mod12_residual_degree (b b' : ℕ) (hb' : 6 ≤ b') (hbb : b' ≤ b)
    (M' : Predicate b') (hM : IsResidual (mod12 b) M') :
    b' - 5 ≤ algebraicDegree M' ∧ algebraicDegree M' ≤ b' := by sorry

end GoldreichAffine.Exponential.Supplement
