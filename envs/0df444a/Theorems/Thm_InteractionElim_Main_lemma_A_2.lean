-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_A_2
-- name    : InteractionElim.Main.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:20:23.62447+00:00
-- url     : https://prove2.me/theorems/51768bd1-ea0a-49f5-aeed-9c48d8cba067
-- title:
--   Lemma A.2 — saturated extraction: $F(W)\le4(d+T)$ for any distribution on a $W^\perp$-saturated cell
-- statement:
--   Let $W\le\mathbb F_2^r$, let $D\ne\emptyset$ be $W^\perp$-saturated ($D+W^\perp=D$), and let $p$ be any probability distribution on $\mathbb F_2^r$ supported on $D$. Put $d=r-H_2(p)$ (the entropy deficit, $H_2$ the base-two entropy) and $T=\mathbb E_p\,\tau(X,D)=\sum_z p(z)\tau(z,D)$. Then
--   $$
--   F(W)\le 4(d+T).
--   $$
--   This converts a posterior over a complete saturated compatibility cell, with its entropy deficit and average certificate, into a bound on the geometric objective $F$; the converse (Proposition B.3) uses it.
--
--   **Formalization Note** The distribution is a function $p\ge0$ with $\sum_z p(z)=1$ and $p(z)=0$ off $D$; $0\log_20=0$.
--
--   Differences from the source:
--   - encoding: p any distribution supported on D → p : F_2^r → ℝ with p ≥ 0, ∑ p = 1 and p = 0 off D; reason: a distribution on a finite set is its mass function
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 18, Lemma A.2, Eq. (A.5)

import Mathlib
import Definitions.Def_InteractionElim_Main_Certificate

open scoped BigOperators

namespace InteractionElim.Main

theorem lemma_A_2 (r : ℕ) (W : Submodule (ZMod 2) (Fin r → ZMod 2))
    (D : Finset (Fin r → ZMod 2)) (hD : D.Nonempty)
    (hsat : Saturated (D : Set (Fin r → ZMod 2)) (orth W))
    (p : (Fin r → ZMod 2) → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hp_supp : ∀ z, z ∉ D → p z = 0) :
    F W ≤ 4 * (((r : ℝ) - entropy2 p) + ∑ z, p z * tau z (D : Set (Fin r → ZMod 2))) := by sorry

end InteractionElim.Main
