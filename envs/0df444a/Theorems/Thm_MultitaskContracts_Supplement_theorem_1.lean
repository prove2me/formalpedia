-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_1
-- name    : MultitaskContracts.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:06:57.979986+00:00
-- url     : https://prove2.me/theorems/72acf122-095d-4760-8157-156e138ab6d6
-- title:
--   Theorem 1 — under independence, $t^\star=\max_{0\le\ell<|K|}\theta(S_\ell)$ over the prefixes of the stand-alone order
-- statement:
--   Let $I$ be an instance of the multitask model with independent tasks on a finite nonempty task set $K$. The **stand-alone payment** of task $k$ is $c_k/(1-q_k/p_k)$ (Definition 4), the **incentive price** of a strategy $S\subsetneq K$ is $\theta(S)=\dfrac{c(K)-c(S)}{P_K(K)-P_S(K)}$ (Definition 3), and $t^\star=\max_{S\subsetneq K}\theta(S)$ (eq. (10)).
--
--   Let $k_{(1)},\dots,k_{(|K|)}$ be the tasks in ascending order of stand-alone payment, with ties broken arbitrarily, and let $S_\ell:=\{k_{(1)},\dots,k_{(\ell)}\}$. Then
--   $$t^\star\;=\;\max_{0\le\ell<|K|}\theta(S_\ell).$$
--   The identity holds for every such order.
--
--   Only the $|K|$ prefixes of one sorted order need to be examined instead of all $2^{|K|}-1$ deviations. This gives the $O(|K|\log|K|)$ algorithm for optimal Min-Pay contracts with heterogeneous independent tasks (Corollary 2).
--
--   **Formalization Note** The order is any bijection $e:\{0,\dots,|K|-1\}\to K$ along which the stand-alone payment is non-decreasing, and $S_\ell=e(\{i:i<\ell\})$, so $S_0=\emptyset$; $\ell$ ranges over $\{0,\dots,|K|-1\}$.
--
--   Differences from the source:
--   - encoding: the tasks in ascending order of stand-alone payment, with ties broken arbitrarily → every bijection e : Fin |K| ≃ K with standAlone ∘ e monotone, S_ℓ = e({i : i < ℓ}), ℓ : Fin |K|; reason: an ordering of a finite set is a bijection with an initial segment of ℕ; quantifying over every monotone e is "ties broken arbitrarily"
--   - encoding: §4.1 standing assumptions (independent tasks; t⋆ over the deviations of K) → hypothesis I.IsIndependent and [Nonempty K]; reason: the section title "Independent Tasks" and the proof's "By independence" make independence a standing assumption; t⋆ = max over S ⊊ K needs a deviation, so K is nonempty
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Instance_incentivePrice
import Definitions.Def_MultitaskContracts_Instance_tStar
import Definitions.Def_MultitaskContracts_Instance_standAlone

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 1** (§4.1.2, p.14, PDF 16). Let `k(1), …, k(|K|)` be the tasks in ascending order
of stand-alone payment (Definition 4), with ties broken arbitrarily. Then
`t⋆ = max_{0≤ℓ<|K|} θ(S_ℓ)`, where `S_ℓ := {k(1), …, k(ℓ)}`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 1, p.14.

**Formalization Note.** §4.1 assumes independent tasks (`hI`), and `t⋆` (published
`Instance.tStar`, eq. (10)) needs `K` nonempty. The order is any bijection
`e : Fin |K| ≃ K` along which the stand-alone payment (published `Instance.standAlone`) is
monotone; quantifying over every such `e` is "ties broken arbitrarily". `ℓ` ranges over
`Fin |K|`, i.e. `0 ≤ ℓ < |K|`, and `S_ℓ` is the image under `e` of `{i : i < ℓ}`
(`S_0 = ∅`). `θ` is the published `Instance.incentivePrice`. -/
theorem theorem_1 {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K] (I : Instance K)
    (hI : I.IsIndependent) (e : Fin (Fintype.card K) ≃ K) (he : Monotone (I.standAlone ∘ e)) :
    I.tStar = (Finset.univ : Finset (Fin (Fintype.card K))).sup'
      (Finset.univ_nonempty_iff.2 ⟨⟨0, Fintype.card_pos⟩⟩)
      (fun ℓ => I.incentivePrice
        (((Finset.univ : Finset (Fin (Fintype.card K))).filter (fun i => i.val < ℓ.val)).map
          e.toEmbedding)) := by sorry

end MultitaskContracts.Supplement
