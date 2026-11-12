-- Prove2me | Theorems.Thm_NarrowDNF_Approx_lemma_3_4
-- name    : NarrowDNF.Approx.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:29.035358+00:00
-- url     : https://prove2.me/theorems/f47ac755-3513-4942-8306-97f88bba2f8b
-- title:
--   Lemma 3.4 — Load transport
-- statement:
--   Let $0<p<1$, let $d$ be a nonnegative integer, and let $J$ be any local activation family with $J_S\equiv0$ whenever $|S|>d$. Let $D$ be a random coordinate subset with independent inclusion probability $p$, independently of the input, and put $p'=2p-p^2$. Then
--   $$\mathbb E_D\Lambda_p(J^D)=\Lambda_{p'}(J)\le(2-p)^d\Lambda_p(J)\le2^d\Lambda_p(J).$$
--   Consequently,
--   $$\mathbb E_D\mathbb E_p|A_{J^D}(X)|\le(2-p)^d\Lambda_p(J).$$
--   No increasing-activation hypothesis is imposed. The same family defines every load, with only the bias changed. This retains the exact transport identity, the sharper likelihood bound and the active-union consequence, also when $d=0$.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: local activations on the labels in each coordinate subset S → dependent functions (S : Finset (Fin n)) → (S → Bool) → Bool; reason: this enforces exactly the source locality while allowing arbitrary, nonmonotone activations
--   - encoding: nonnegative integer cutoffs → natural numbers; reason: the domains coincide, including zero
--   - encoding: a product-random subset D independent of X → an outer cube expectation over its ones-set with an inner expectation under the same bias; reason: nested finite product sums give the independent joint law
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 3.4, Eq. (6), p. 7 (PDF p. 8)

import Definitions.Def_NarrowDNF_Approx_Activation

namespace NarrowDNF.Approx

theorem lemma_3_4 {n : ℕ} (p : ℝ) (d : ℕ) (J : ActivationFamily n)
    (hp : 0 < p) (hp_one : p < 1) (hd : ArityLE J d) :
    expect p (fun z => load p (force J (ones z))) = load (2 * p - p ^ 2) J ∧
    load (2 * p - p ^ 2) J ≤ (2 - p) ^ d * load p J ∧
    (2 - p) ^ d * load p J ≤ (2 : ℝ) ^ d * load p J ∧
    expect p (fun z => activeCost p (force J (ones z))) ≤ (2 - p) ^ d * load p J := by sorry

end NarrowDNF.Approx
