-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_modular_advantage_criterion
-- name    : GoldreichAffine.Exponential.Supplement.modular_advantage_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:34.736023+00:00
-- url     : https://prove2.me/theorems/20cece04-4447-4f74-97b1-fcd370229eeb
-- title:
--   Theorem 3 — vanishing bit-fixing affine advantage of MOD$^{t,S_0}$ iff $4\mid t$ and balanced parities
-- statement:
--   Fix an integer $t\ge2$ and a residue set $S_0\subseteq[t]=\{0,\dots,t-1\}$. Then
--
--   $$\lim_{b'\to\infty}\ \sup_{b\ge b'}\ \operatorname{adv}_{b'}\big(\mathsf{MOD}^{t,S_0}_b\big)=0$$
--
--   if and only if $4\mid t$ and
--
--   $$|S_0\cap2\mathbb Z|=|S_0\cap(2\mathbb Z+1)|=\frac t4 .$$
--
--   Here $\operatorname{adv}_{b'}$ is the bit-fixing affine advantage at $b'$ remaining inputs. The limit condition is: for every $\varepsilon>0$ there is $B$ such that $|\operatorname{adv}_{b'}(\mathsf{MOD}^{t,S_0}_b)|\le\varepsilon$ for all $b'\ge B$ and all $b\ge b'$.
--
--   This companion theorem shows that vanishing bit-fixing affine advantage of a modular predicate requires a modulus divisible by four, which singles out $12$ as the smallest candidate modulus with unbounded degree.
--
--   Differences from the source:
--   - encoding: lim_{b′→∞} sup_{b≥b′} adv_{b′}(MOD_b^{t,S0}) = 0 → ∀ε>0 ∃B ∀b′≥B ∀b≥b′, |adv_{b′}(MOD_b^{t,S0})| ≤ ε; reason: for b′ ≤ b the advantage lies in [0,1/2] (an affine function and its complement are both affine), so the sup exists and tends to 0 exactly when eventually every term is at most ε
--   - encoding: |S0 ∩ 2Z| = |S0 ∩ (2Z+1)| = t/4, S0 ⊆ [t] → (S0.filter Even).card = t/4 ∧ (S0.filter Odd).card = t/4, S0 ⊆ Finset.range t; reason: same sets; t/4 is exact division once 4 ∣ t, which is the first conjunct
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 10 (PDF p. 11), Theorem 3; proof App. B.2, pp. 27–29 (PDF pp. 28–30)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 3, printed p.10 / PDF p.11: lim_{b'→∞} sup_{b≥b'} adv_{b'}(MOD^{t,S0}_b) = 0
    iff 4 ∣ t and S0 has exactly t/4 even and t/4 odd residues. -/
theorem modular_advantage_criterion (t : ℕ) (S0 : Finset ℕ) (ht : 2 ≤ t)
    (hS0 : S0 ⊆ Finset.range t) :
    (∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ b' : ℕ, B ≤ b' → ∀ b : ℕ, b' ≤ b →
        |advantage (modPredicate t S0 b) b'| ≤ ε) ↔
      (4 ∣ t ∧ (S0.filter Even).card = t / 4 ∧ (S0.filter Odd).card = t / 4) := by sorry

end GoldreichAffine.Exponential.Supplement
