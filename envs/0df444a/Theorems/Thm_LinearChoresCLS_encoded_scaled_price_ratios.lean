-- Prove2me | Theorems.Thm_LinearChoresCLS_encoded_scaled_price_ratios
-- name    : LinearChoresCLS.encoded_scaled_price_ratios
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:39:47.750057+00:00
-- url     : https://prove2.me/theorems/e9f487ac-ce19-4b42-be65-d9103e65788e
-- title:
--   Polynomial-time scaled basic-price ratios from encoded market parameters and prices
-- statement:
--   Fix a dimension $n$, a chain length $L$, and an encoded rational price-allocation pair $(p,z)$. Suppose $b$ selects the first $n+1$ coordinates of the price vector, in order, and $p_{b(0)}>0$. There is a deterministic polynomial-time procedure which reads the tagged pair consisting of the encodings of $(n,L)$ and $(p,z)$ and returns the rational-vector encoding of
--
--   $$
--   \left(2^L\left(\frac{p_{b(i+1)}}{p_{b(0)}}-1\right)\right)_{i=0}^{n-1}.
--   $$
--
--   This is precisely the arithmetic part of decoder (7.3), since $t=2^{-L}$ and hence $1/t=2^L$. Only the encoded price vector is needed; the allocation suffix need not be interpreted. No equilibrium hypothesis is required.
--
--   **Formalization Note** The map is total and polynomial-time in Cook's one-tape machine model on all tagged words. The hypothesis $(b j).val=j.val$ supplies the coordinate identification used by (7.3), while positivity of the base price ensures that the displayed ratio is the genuine price ratio.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1, https://arxiv.org/html/2611.06589v1, Section 7.1, equations (7.1) and (7.3), pp.30–32: t=2^{-L} and g(I,(p,z))=(1/t)(p_1/p_0-1,...,p_n/p_0-1), computed in polynomial time from I and the equilibrium prices.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem LinearChoresCLS.encoded_scaled_price_ratios :
    ∃ h : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime h ∧
      ∀ {n a m : ℕ} (L : ℕ) (b : Fin (n+1) → Fin m),
        (∀ j, (b j).val = j.val) →
        ∀ (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ), 0 < p (b 0) →
        encVector (fun i : Fin n =>
          (1 / ((1/2 : ℚ)^L)) * (p (b i.succ) / p (b 0) - 1)) =
        h (pairCode (encNat n ++ encNat L) (encCE p z)) := by sorry
