-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_binomial_transform_identity
-- name    : GoldreichAffine.Exponential.Supplement.binomial_transform_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:04.373714+00:00
-- url     : https://prove2.me/theorems/a8ba1bfa-8b76-4374-bb9b-4ee9c87b2f0e
-- title:
--   Lemma 7 — binomial transform identity $\lambda_{j+2^k}(w)=\lambda_j(w)+\lambda_j(w+2^k)$
-- statement:
--   For a binary sequence $a=(a(h))_{h\ge0}$ over $\mathbb F_2$ let $\lambda^a_j(w)=\sum_{h=0}^{j}\binom jh a(w+h)$ in $\mathbb F_2$. For every modular function $\mathsf{MOD}^{t,S_0}_b$ ($t\ge2$, $S_0\subseteq[t]$), whose coefficients are $\lambda_j(w)=\lambda^a_j(w)$ with $a(h)=(1-g_{t,S_0}(h))/2$, and for all integers $j,k,w\ge0$,
--
--   $$\lambda_{j+2^k}(w)=\lambda_j(w)+\lambda_j(w+2^k).$$
--
--   The identity also holds for the binomial transform $\lambda^a$ of any binary sequence $a$.
--
--   The identity is the tool behind the periodicity of the ANF coefficients of MOD12 (Lemma 8), and hence behind the degree bound of Theorem 4.
--
--   Differences from the source:
--   - encoding: coefficients over F₂ of MOD^{t,S0}_b, and of an arbitrary binary sequence → binomialTransform over ZMod 2 of modSequence t S0 (first conjunct) and of any a : ℕ → ZMod 2 (second conjunct); reason: ZMod 2 is F₂; λ_j(w) does not depend on b, so the MOD clause needs no b
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 30 (PDF p. 31), Lemma 7; proof pp. 30–31 (PDF pp. 31–32)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Lemma 7, printed p.30 / PDF p.31: lambda_{j+2^k}(w) = lambda_j(w) + lambda_j(w+2^k) over F₂,
    for the coefficients of every MOD^{t,S0} and for the binomial transform of any binary sequence. -/
theorem binomial_transform_identity :
    (∀ (t : ℕ) (S0 : Finset ℕ), 2 ≤ t → S0 ⊆ Finset.range t → ∀ j k w : ℕ,
      binomialTransform (modSequence t S0) (j + 2 ^ k) w =
        binomialTransform (modSequence t S0) j w +
          binomialTransform (modSequence t S0) j (w + 2 ^ k)) ∧
    (∀ (a : ℕ → ZMod 2) (j k w : ℕ),
      binomialTransform a (j + 2 ^ k) w =
        binomialTransform a j w + binomialTransform a j (w + 2 ^ k)) := by sorry

end GoldreichAffine.Exponential.Supplement
