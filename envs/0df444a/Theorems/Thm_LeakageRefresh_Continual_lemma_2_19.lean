-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_2_19
-- name    : LeakageRefresh.Continual.lemma_2_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:00.889367+00:00
-- url     : https://prove2.me/theorems/25863a4a-ef64-44f7-9b76-3069f5da8343
-- title:
--   Lemma 2.19 — freshness: a uniform invertible refresh sends every encoding of $s$ to a uniform encoding of $s$
-- statement:
--   Let $n\ge2$, $s\in\mathbb F_2$ and $(\ell,r)\in\Omega_s$, and let $M$ be uniform on $\mathrm{InvMatr}^n_2$. Then the refreshed pair $(\ell\cdot M,\ M^{-1}\cdot r)$ has distribution $\mu_s$: for every state $y\in U_L\times U_R$,
--   $$\Pr_M\big[(\ell M,\ M^{-1}r)=y\big]=\mu_s(y).$$
--   This is the freshness property behind the exact independent-encoding experiment of §4.2: a refresh forgets everything about the old state except the encoded bit.
--
--   Differences from the source:
--   - encoding: "has distribution $\mu_s$" → for every state $y$, $\#\{M:\text{refresh}(M,x)=y\}/|\mathrm{InvMatr}^n_2|=\mu_s(y)$; reason: equality of two distributions on a finite set, written pointwise
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 23, Lemma 2.19

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding

namespace LeakageRefresh.Continual

/-- **Lemma 2.19 (Freshness).** For every `s ∈ F₂` and every `(ℓ, r) ∈ Ωₛ`, if
`M ←$ InvMatrⁿ₂`, the refreshed pair `(ℓ · M, M⁻¹ · r)` has distribution `µₛ`: for every state
`y`, the probability that it equals `y` is `µₛ(y)`. -/
theorem lemma_2_19 (n : ℕ) (hn : 2 ≤ n) (s : ZMod 2) (x : State n) (hx : x ∈ Omega n s)
    (y : State n) :
    ((Finset.univ.filter (fun M : InvMatr n => refreshState M x = y)).card : ℝ) /
        (Fintype.card (InvMatr n) : ℝ) = mu n s y := by sorry

end LeakageRefresh.Continual
