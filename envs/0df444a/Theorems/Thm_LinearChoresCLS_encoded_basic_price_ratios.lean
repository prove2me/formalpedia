-- Prove2me | Theorems.Thm_LinearChoresCLS_encoded_basic_price_ratios
-- name    : LinearChoresCLS.encoded_basic_price_ratios
-- status  : Open
-- author  : @Weiqiang
-- created : 2026-11-13T20:43:39.526961+00:00
-- url     : https://prove2.me/theorems/9b4cad1f-c649-4e89-9781-62bf6300f70a
-- title:
--   Polynomial-time extraction of the rational basic-price ratios
-- statement:
--   Let $(P,\varepsilon)$ be a valid rational source instance of dimension $n$. Let $p$ be a rational price vector with at least $n+1$ entries and positive first entry, and $z$ any rational allocation matrix of compatible dimensions. There is a polynomial-time function of the tagged pair of the source word and the price–allocation word that returns the public rational-vector encoding of
--   $$\left(2^L(p_i/p_0-1)\right)_{i=1}^n,$$
--   where $L$ is the dyadic exponent determined by the source. Correctness concerns the first $n+1$ price entries and holds without any equilibrium condition.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1. https://arxiv.org/html/2611.06589v1 Section 7.1, equation (7.3) and Completing the Verification.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

namespace LinearChoresCLS

open NetworkEquilibriumCLS.LinearNash in
theorem encoded_basic_price_ratios :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime g ∧
      ∀ {n a m : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        ∀ (b : Fin (n+1) → Fin m), (∀ j, (b j).val = j.val) →
        ∀ (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ), 0 < p (b 0) →
        encVector (fun i : Fin n =>
          (1 / ((1/2 : ℚ)^chainLength P ε)) * (p (b i.succ) / p (b 0) - 1)) =
        g (pairCode (encQuadratic P ++ encRat ε) (encCE p z)) := by sorry

end LinearChoresCLS
