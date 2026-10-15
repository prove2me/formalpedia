-- Prove2me | Theorems.Thm_OAI_BufferedIsing_jointWeight_pos
-- name    : OAI.BufferedIsing.jointWeight_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:11:37.167332+00:00
-- url     : https://prove2.me/theorems/ca26882f-f9ad-4687-8f17-cdeb3616c34d
-- title:
--   Positivity of the pinned joint block weight for pairwise disjoint blocks
-- statement:
--   Let $G$ be a finite graph on $V=\{0,\dots,n-1\}$ whose edges $e$ have endpoints $l(e)\neq r(e)$ and couplings $K_e\ge0$, let $h\in\mathbb{R}^V$ be an arbitrary external field, and let $w_h(\sigma)=\exp\bigl(\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v\bigr)$ be the Ising weight of $\sigma\in\{-1,+1\}^V$. Let $I,J,F\subseteq V$ be pairwise disjoint. Then for all configurations $\tau,a,b\in\{-1,+1\}^V$ the joint weight is strictly positive:
--
--   $$W_{h,\tau}(a,b)=\sum_{\sigma:\ \sigma_I=a_I,\ \sigma_J=b_J,\ \sigma_F=\tau_F}w_h(\sigma)>0 .$$
--
--   Disjointness makes the three prescriptions compatible. The statement guarantees that conditional probabilities of $\sigma_I$ given $\sigma_J$ and $\sigma_F$ are well defined, and that logarithms of joint weights, such as those in the extreme log-odds, are logarithms of positive numbers.
--
--   **Formalization Note** The joint weight is `jointWeight G h I J F τ a b`, with configurations `Fin n → Bool`; the three disjointness hypotheses are `Disjoint I J`, `Disjoint I F` and `Disjoint J F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Basic.lean#L139-L154

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.jointWeight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b : Spins n) : 0 < jointWeight G h I J F τ a b := by sorry
