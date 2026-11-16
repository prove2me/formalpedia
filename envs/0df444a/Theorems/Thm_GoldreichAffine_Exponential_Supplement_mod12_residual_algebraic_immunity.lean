-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_mod12_residual_algebraic_immunity
-- name    : GoldreichAffine.Exponential.Supplement.mod12_residual_algebraic_immunity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:55.770212+00:00
-- url     : https://prove2.me/theorems/6c04a777-baa1-4817-9bea-ca92559537c0
-- title:
--   Theorem 5 — every $b'$-input residual of MOD12 has algebraic immunity ≥ ⌊(b'+1)/3⌋
-- statement:
--   Let $b\ge6$ and $6\le b'\le b$. For every residual $M'\in\mathcal R_{b'}(\mathsf{MOD12}_b)$,
--
--   $$\mathrm{AI}(M')\ge\Big\lfloor\frac{b'+1}3\Big\rfloor .$$
--
--   Consequently $\mathrm{AI}(M')=\Theta(b')$; the upper half is $\mathrm{AI}(M')\le b'$, since the algebraic immunity of any Boolean function on $b'$ inputs is at most $b'$.
--
--   This companion theorem shows that MOD12 keeps algebraic immunity linear in the number of free inputs under every partial fixing.
--
--   Differences from the source:
--   - encoding: b ≥ 6 and 6 ≤ b′ ≤ b → 6 ≤ b′ and b′ ≤ b; reason: b ≥ 6 follows from 6 ≤ b′ ≤ b
--   - encoding: AI(M′) ≥ ⌊(b′+1)/3⌋; consequently AI(M′) = Θ(b′) → (b′ + 1) / 3 ≤ AI M′ ∧ AI M′ ≤ b′; reason: natural division is the floor; the Θ consequence is the floor bound together with AI ≤ b′, the constant the proof gives (PDF p. 35)
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 10 (PDF p. 11), Theorem 5; proof App. B.4, p. 34 (PDF p. 35)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
import Definitions.Def_GoldreichAffine_Exponential_Supplement_Algebraic
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 5, printed p.10 / PDF p.11: AI(M') ≥ ⌊(b'+1)/3⌋ for every M' ∈ R_{b'}(MOD12_b),
    6 ≤ b' ≤ b; the second conjunct AI(M') ≤ b' is the upper half of AI(M') = Θ(b')
    with the constant of the proof (PDF p.35). -/
theorem mod12_residual_algebraic_immunity (b b' : ℕ) (hb' : 6 ≤ b') (hbb : b' ≤ b)
    (M' : Predicate b') (hM : IsResidual (mod12 b) M') :
    (b' + 1) / 3 ≤ algebraicImmunity M' ∧ algebraicImmunity M' ≤ b' := by sorry

end GoldreichAffine.Exponential.Supplement
