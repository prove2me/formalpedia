-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_theorem_1
-- name    : MultiPriceOnline.Balance.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:46.690301+00:00
-- url     : https://prove2.me/theorems/8fe80f62-8887-4d4a-9b04-0598bdd2292e
-- title:
--   Theorem 1, p. 16 — Multi-price Balance is minᵢ bᵢ-competitive, bᵢ ∈ {F(𝒫ᵢ)/((1+kᵢ)(e^{1/kᵢ}−1)), G(𝒫ᵢ)/2, (1−1/e)/((1+kᵢ)(1−e^{−1/kᵢ}))}
-- statement:
--   Consider any setup of the multi-price online allocation problem. There is a nonempty finite set of items; item $i$ has starting inventory $k_i\ge1$ and price set $\mathcal P_i=\{r_i^{(1)}<\dots<r_i^{(m_i)}\}$ with $r_i^{(1)}>0$ and $m_i\ge1$. Item $i$ has booking limits $\alpha_i$ from (7) and values $\sigma_i$ from (8), so that $F(\mathcal P_i)=1-e^{-\alpha_i^{(1)}}$ and $G(\mathcal P_i)=\sigma_i^{(1)}$.
--
--   Choose for each item a mode, *perturb* or *split*, and run Multi-price Balance (Algorithm 1) with those modes. A perturbed item uses the randomized procedure of Definition 3. A split item is replaced by $k_i$ single-unit items with its prices and purchase probabilities, each using the procedure (45). Let
--   $$
--   b_i=\begin{cases}\dfrac{G(\mathcal P_i)}{2}&\text{if $i$ is split},\\[8pt]\dfrac{1-1/e}{(1+k_i)(1-e^{-1/k_i})}&\text{if $i$ is perturbed and }|\mathcal P_i|=1,\\[8pt]\dfrac{F(\mathcal P_i)}{(1+k_i)(e^{1/k_i}-1)}&\text{if $i$ is perturbed and }|\mathcal P_i|\ge2.\end{cases}
--   $$
--   Then Multi-price Balance achieves a competitive ratio of $\min_i b_i$. Take any number of customers $T$, any purchase probabilities $p^{(j)}_{t,i}\in[0,1]$, any tie-breaking rule offering a maximizer of (16), and any feasible solution $x$ of the LP (5) of the original setup. Then
--   $$
--   \Big(\min_i b_i\Big)\cdot\sum_{t=1}^T\sum_i\sum_{j=1}^{m_i}p^{(j)}_{t,i}r_i^{(j)}x^{(j)}_{t,i}\ \le\ \mathbb E[\mathrm{ALG}(\mathcal S,\mathcal A)].
--   $$
--
--   This is the main positive result of the paper for general purchase probabilities. As inventories grow, bound (i) tends to $F(\mathcal P_i)$, which Theorem 3 shows cannot be beaten by any online algorithm.
--
--   **Formalization Note** The paper states Theorem 1 as "a competitive ratio of $\min_i\tilde F_i$". There $\tilde F_i$ is the optimum of the problem (44) with $k=k_i$, and the theorem asserts $\tilde F_i\ge$ (i), (ii), and (iii) if $|\mathcal P_i|=1$. The proof (App. B.3) obtains bound (ii) by splitting item $i$ into $k_i$ single-unit items. That is a run of Algorithm 1 on a different setup, not a procedure feasible for (44) with $k=k_i$. The paper also never shows that the supremum in (44) is attained. So $\tilde F_i$ is not used here: the theorem is stated with the explicit bounds and a mode per item, which is what App. B.3 proves. Choosing for each item the mode with the larger bound gives the printed form $\min_i\max\{(\mathrm i),(\mathrm{ii}),(\mathrm{iii})\text{ if }|\mathcal P_i|=1\}$, because (iii) $\ge$ (i) when $|\mathcal P_i|=1$. For $|\mathcal P_i|=1$, $\alpha_i^{(1)}=1$ and $1-e^{-\alpha_i^{(1)}}=1-1/e$. The competitive ratio (6) is stated multiplied out for every feasible $x$ of the original LP (5), so no division by $\mathrm{OPT}$ occurs. The benchmark is the original setup's LP, not the split setup's. The procedures depend only on the setup and the modes; the arrival sequence and the tie-breaking rule are quantified after them. Items form a nonempty finite type, so that the minimum exists; with no items both sides would be $0$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 16, Theorem 1; proof in App. B.3, pp. 44–45

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_LP
import Definitions.Def_MultiPriceOnline_Balance_Procedure
import Definitions.Def_MultiPriceOnline_Balance_Algorithm

namespace MultiPriceOnline.Balance

/-- Theorem 1 (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 16; proof in App. B.3, pp. 44–45), with its
explicit bounds. For any setup (a nonempty finite set of items, item `i` with inventory `kᵢ ≥ 1`,
price set `0 < rᵢ⁽¹⁾ < … < rᵢ⁽ᵐⁱ⁾`, booking limits `αᵢ` of (7) and values `σᵢ` of (8)) and any choice
of modes (`split i`), Multi-price Balance with those modes achieves the competitive ratio
`minᵢ bᵢ`, where `bᵢ = G(𝒫ᵢ)/2` for a split item, `(1 − 1/e)/((1 + kᵢ)(1 − e^{−1/kᵢ}))` for an
unsplit item with `|𝒫ᵢ| = 1`, and `F(𝒫ᵢ)/((1 + kᵢ)(e^{1/kᵢ} − 1))` for an unsplit item with
`|𝒫ᵢ| ≥ 2`: for every arrival sequence, every tie-breaking rule maximizing (16) and every feasible
solution `x` of the LP (5) of the original setup, `(minᵢ bᵢ) · (5a)(x) ≤ 𝔼[ALG]`. -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (k m : ι → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hm : ∀ i, 1 ≤ m i) (r α σ : ι → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, IsBookingLimits (m i) (r i) (α i))
    (hσ : ∀ i, IsBQLimits (m i) (r i) (σ i)) (split : ι → Bool)
    {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1)
    (sel : Selector (fun x : SplitItem k split => m x.1)) (hsel : IsArgmaxSelector sel)
    (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x) :
    (Finset.univ.inf' Finset.univ_nonempty
        (fun i => modeBound (k i) (m i) (α i) (σ i) (split i))) * lpObj m r p x ≤
      balanceRevenue k m r α σ split sel p := by sorry

end MultiPriceOnline.Balance
