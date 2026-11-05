-- Prove2me | Theorems.Thm_MayersQKD_rhoX_entry
-- name    : MayersQKD.rhoX_entry
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:50.966806+00:00
-- url     : https://prove2.me/theorems/ac535bdd-5aca-4977-9d05-7e49c6dbcc6e
-- title:
--   Closing display of §9, p.12 — the matrix of $\rho_x$ (corrected: $f$ of full row rank)
-- statement:
--   Let $\hat\theta$ be opposite to $\theta$ at every position, let $f$ have rank $r+m$, and let $\beta\in C_x$. Then, in Bob's basis,
--
--   $$
--   (\rho_x)_{\alpha,\alpha'}=2^{-N}\times\begin{cases}0&\text{if }(\alpha\oplus\alpha')\notin C_{\mathbf 0}^\perp,\\(-1)^{(\alpha\oplus\alpha')\odot\beta}&\text{otherwise,}\end{cases}
--   $$
--
--   where $C_{\mathbf 0}^\perp$ is the span of the rows of $f$.
--
--   It follows that two matrices $\rho_x,\rho_{x'}$ differ only at entries with $\alpha\oplus\alpha'$ a nonzero codeword of $C_{\mathbf 0}^\perp$, which is the fact Lemma 1 uses.
--
--   **Formalization Note** Rank is taken over $\mathrm{GF}(2)$.
--
--   Differences from the source:
--   - correction: no hypothesis on f → f has rank r + m; reason: false without it: N = 2, r = 0, m = 2, f = ((1,1),(1,1)) gives k = 0 and ρ₀ = |ψ₀₀⟩⟨ψ₀₀| + |ψ₁₁⟩⟨ψ₁₁|, whose diagonal entries in the opposite basis are 1/2, not 2⁻² (correction C1)
--   - reading: (α⊕α′)⊗β in the exponent → (α⊕α′)⊙β; reason: ⊗ is a misprint: it must be the scalar of formula (4)
--   - encoding: the exponent in GF(2) → its value in {0, 1}; reason: Lean power needs a natural exponent; the sign is the same
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §9, closing display, p.12; §8, p.11

import Mathlib
import Definitions.Def_MayersQKD_rhoX

namespace MayersQKD

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §9, closing display, p.12 (also §8, p.11): for `f` of rank
`r + m` and every `β ∈ C_x`, in Bob's basis, `(ρ_x)_{α,α′}` is `0` if `α ⊕ α′ ∉ C₀⊥` and
`2⁻ᴺ (−1)^((α⊕α′)⊙β)` otherwise.

**Formalization Note.** The printed `⊗` is `⊙`. `C₀⊥` is the span of the rows of `f` (p.10). The rank
hypothesis is correction C1: `k = N − r − m` is used as the dimension of `C₀`, which needs
independent rows. -/
theorem rhoX_entry {N r m : ℕ} (θ θhat : Bases N) (hθ : ∀ i, θhat i ≠ θ i)
    (f : HashMatrix r m N) (hf : f.rank = r + m) (x : Fin r ⊕ Fin m → ZMod 2) (β : Bits N)
    (hβ : f.mulVec β = x) (α α' : Bits N) :
    matEntry θhat (rhoX f θ x) α α' =
      (1 / 2 : ℂ) ^ N *
        (if α + α' ∈ rowCode f then (-1 : ℂ) ^ ((α + α') ⬝ᵥ β).val else 0) := by sorry

end MayersQKD
