-- Prove2me | Theorems.Thm_MayersQKD_rhoPrefix_entry
-- name    : MayersQKD.rhoPrefix_entry
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:30.916392+00:00
-- url     : https://prove2.me/theorems/6cf0a9b0-f8df-480c-882e-3dc93e1814ef
-- title:
--   (5), p.12 — the matrix of $\rho^{(j)}$
-- statement:
--   Let $\hat\theta$ be opposite to $\theta$ at every position, let $\beta_1,\dots,\beta_k$ be linearly independent in $\mathrm{GF}(2)^N$, and let $0\le j\le k$. Then, in Bob's basis,
--
--   $$
--   (\rho^{(j)})_{\alpha,\alpha'}=2^{-N}\times\begin{cases}0&\text{if }(\alpha\oplus\alpha')\notin C^{(j)\perp},\\1&\text{otherwise.}\end{cases}
--   $$
--
--   At $j=k$ this is the matrix of $\rho_{\mathbf 0}$.
--
--   Differences from the source:
--   - generalization: {β₁, …, β_k} a basis of C₀ with k = N − m − r → any linearly independent family of any length k; reason: every such basis is such a family; (5) uses no other property of C₀
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §9, (5), p.12

import Mathlib
import Definitions.Def_MayersQKD_rhoX

namespace MayersQKD

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §9, (5), p.12: for `j = 0, …, k`, in Bob's basis,
`(ρ^(j))_{α,α′}` is `2⁻ᴺ` if `α ⊕ α′ ∈ C^(j)⊥` and `0` otherwise.

**Formalization Note.** Positions are those of `E₁`, so `θ̂` is opposite to `θ` everywhere (§9, p.11).
The family `β₁, …, β_k` is any linearly independent family: every such family is a basis of its
span, which is the `C₀` of a suitable `f`. The page's "`GF(2)ⁿ`" in §9 is `GF(2)ᴺ`. -/
theorem rhoPrefix_entry {N k : ℕ} (θ θhat : Bases N) (hθ : ∀ i, θhat i ≠ θ i)
    (bs : Fin k → Bits N) (hbs : LinearIndependent (ZMod 2) bs) (j : ℕ) (hj : j ≤ k)
    (α α' : Bits N) :
    matEntry θhat (rhoPrefix bs θ j) α α' =
      (1 / 2 : ℂ) ^ N * (if α + α' ∈ dualCode (prefixSpan bs j) then 1 else 0) := by sorry

end MayersQKD
