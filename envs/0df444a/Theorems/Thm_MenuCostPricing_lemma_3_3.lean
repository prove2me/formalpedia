-- Prove2me | Theorems.Thm_MenuCostPricing_lemma_3_3
-- name    : MenuCostPricing.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:18.741243+00:00
-- url     : https://prove2.me/theorems/03836822-92b0-4e4c-b396-66c1a275efd2
-- title:
--   Lemma 3.3 — $(1-(\alpha+\beta))R(x)\le\hat{\mathcal R}_{\alpha,\beta}(x)\le(1+(\alpha+\beta)\varrho_{\max})R(x)$
-- statement:
--   Let $\alpha,\beta\in[0,1]$, let $\Gamma\subseteq[2,T]$ and $\hat w$ be guesses, and let $x$ be a pricing strategy feasible to APX$(\alpha,\beta)$. Then
--   $$
--   (1-(\alpha+\beta))\cdot R(x)\le\hat{\mathcal R}_{\alpha,\beta}(x)\le(1+(\alpha+\beta)\cdot\varrho_{\max})\cdot R(x).
--   $$
--
--   The proxy reward is thus a two-sided approximation of the true expected revenue on the feasible set of APX$(\alpha,\beta)$, which reduces Theorem 3.1 to an approximation scheme for the proxy problem.
--
--   Differences from the source:
--   - generalization: the guesses Γ∗ and ŵ of §3.3 → any Γ ⊆ [2, T] and any ŵ; reason: APX(α, β) and the proof use them only as data; specializes to Γ∗ and the guessed ŵ
--   - encoding: Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν), each customer making an MNL choice; Nₜ independent across periods; D̂ᵗᵢ a sum of Nₜ i.i.d. Bernoulli(q̂) variables → demandLaw: per period, Nₜ from the listed masses, then Nₜ i.i.d. categorical choices on Option (Fin n) counted per product, periods independent (Measure.pi); proxyPathLaw: per product, Nₜ then a sum of Nₜ i.i.d. Bernoulli, periods independent; reason: the paper's joint model written as PMFs; R and R̂ are the printed sums of expectations under these laws
--   - encoding: Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(wᵗ_{i,xᵢ}/(1 + (1 + β)ŵₜ)) → Bernoulli with parameter clamped to [0, 1] (bern); reason: for a strategy feasible to APX(α, β) under Standing the parameter lies in [0, 1], so the clamp changes no instance the paper considers; it makes R̂ⁱ defined for every single-product strategy, which §3.6 evaluates
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Lemma 3.3, p.17; proof App. B.2, pp.46–48

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Lemma 3.3, p.17 (proof App. B.2, pp.46–48): "For
any pricing strategy x feasible to APX(α, β), we have
(1 − (α + β))·R(x) ≤ R̂_{α,β}(x) ≤ (1 + (α + β)·ϱmax)·R(x)", with `α, β ∈ [0, 1]` (p.16).

**Formalization Note.** `Γ` is any set of periods in `[2, T]` and `ŵ` any guess vector; `R̂_{α,β}`
does not depend on `α` (p.17). -/
theorem lemma_3_3 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (Γ : Finset (Fin T))
    (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (x : Strategy n L T) (hx : I.APX Γ ŵ α β x) :
    (1 - (α + β)) * I.R x ≤ I.Rhat ŵ β x ∧
      I.Rhat ŵ β x ≤ (1 + (α + β) * I.rhoMax) * I.R x := by sorry

end MenuCostPricing
