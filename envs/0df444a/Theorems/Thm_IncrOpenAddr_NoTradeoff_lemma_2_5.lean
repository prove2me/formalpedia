-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_2_5
-- name    : IncrOpenAddr.NoTradeoff.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:35:32.071259+00:00
-- url     : https://prove2.me/theorems/349095c9-6706-4316-8ba6-96c3db36565a
-- title:
--   Lemma 2.5 — monotone functions of bin loads on disjoint bin sets satisfy the Chernoff bounds (4)–(5) and the product bound
-- statement:
--   **Lemma 2.5 (Monotone functions of bin loads).** Throw $N$ balls into a finite set of bins independently, ball $b$ according to its own distribution $p_b$ (a ball may land in no bin). Let $G_1,\dots,G_k$ be pairwise disjoint sets of bins, and let each $Y_\ell\in\{0,1\}$ be a function of the loads of the bins in $G_\ell$, where either every $Y_\ell$ is nondecreasing in the loads or every $Y_\ell$ is nonincreasing. Let $Y=\sum_\ell Y_\ell$ and $\mu=\mathbb E[Y]$. Then, as if the $Y_\ell$ were independent (Lemma 2.4):
--   $$\mathbb P\big(Y\le(1-\delta)\mu\big)\le e^{-\delta^2\mu/2},\qquad \mathbb P\big(Y\ge(1+\delta)\mu\big)\le e^{-\delta^2\mu/(2+\delta)}\qquad(\delta>0),\tag{4}$$
--   $$\mathbb P(Y\ge a)\le\Big(\frac{e\bar\mu}{a}\Big)^{a}\qquad\text{whenever }\mu\le\bar\mu<a,\tag{5}$$
--   and $\mathbb P(Y_\ell=1\text{ for all }\ell\in S)\le\prod_{\ell\in S}\mathbb P(Y_\ell=1)$ for every $S\subseteq\{1,\dots,k\}$.
--
--   This is the negative-association tool [DR98, Waj17] that lets the analysis apply Chernoff bounds to counts of bad subtrees, which are not independent.
--
--   **Formalization Note.** $Y_\ell$ is given as a Boolean function $F_\ell$ of the whole load vector that depends only on the loads in $G_\ell$ (`hloc`) and is monotone (resp. antitone) for the pointwise order, `false < true`.
--
--   Differences from the source:
--   - encoding: each Y_ℓ ∈ {0,1} a function of the loads of the bins in G_ℓ → a Boolean function F ℓ of the full load vector with F ℓ L = F ℓ L' whenever L and L' agree on G ℓ; reason: the same functions
--   - encoding: 'Y satisfies the bounds of Lemma 2.4' → the three inequalities (4), (5) of Lemma 2.4 written out for Y, with µ = E[Y] and real exponent a in (5); reason: Lemma 2.4 is not a separate item; its bounds are spelled out
--   - reading: bins (unspecified on the page) → a finite type β of bins; reason: the cited setting [DR98] throws balls into finitely many bins, and every use in the paper (the nodes of one tree T_i) has finitely many
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 11 (PDF 12), Lemma 2.5 (with the bounds (4)–(5) of Lemma 2.4)

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_BallsBins

namespace IncrOpenAddr.NoTradeoff

theorem lemma_2_5 (β : Type) [Fintype β] [DecidableEq β] (N : ℕ)
    (p : Fin N → Option β → ℝ) (hp : IsBallLaw p)
    (k : ℕ) (G : Fin k → Finset β) (hG : Pairwise fun a b => Disjoint (G a) (G b))
    (F : Fin k → (β → ℕ) → Bool)
    (hloc : ∀ (l : Fin k) (L L' : β → ℕ), (∀ x ∈ G l, L x = L' x) → F l L = F l L')
    (hmono : (∀ l, Monotone (F l)) ∨ (∀ l, Antitone (F l))) :
    let Y : (Fin N → Option β) → ℝ := fun ω => ∑ l, if F l (binLoads ω) then (1 : ℝ) else 0
    let μ := ballExp p Y
    (∀ δ : ℝ, 0 < δ →
      ballProb p (fun ω => Y ω ≤ (1 - δ) * μ) ≤ Real.exp (-(δ ^ 2 * μ / 2))) ∧
    (∀ δ : ℝ, 0 < δ →
      ballProb p (fun ω => (1 + δ) * μ ≤ Y ω) ≤ Real.exp (-(δ ^ 2 * μ / (2 + δ)))) ∧
    (∀ μbar a : ℝ, μ ≤ μbar → μbar < a →
      ballProb p (fun ω => a ≤ Y ω) ≤ (Real.exp 1 * μbar / a) ^ a) ∧
    (∀ S : Finset (Fin k),
      ballProb p (fun ω => ∀ l ∈ S, F l (binLoads ω) = true) ≤
        ∏ l ∈ S, ballProb p (fun ω => F l (binLoads ω) = true)) := by sorry

end IncrOpenAddr.NoTradeoff
