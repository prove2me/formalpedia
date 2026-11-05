-- Prove2me | Theorems.Thm_MayersQKD_matEntry_shift
-- name    : MayersQKD.matEntry_shift
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:37.472382+00:00
-- url     : https://prove2.me/theorems/3bb7cd4f-e410-499e-a101-ec3ef6048cb2
-- title:
--   (4), p.12 — $U_\beta\rho U_\beta$ in Bob's basis
-- statement:
--   Let $\hat\theta$ be opposite to $\theta$ at every position. For every operator $\rho$ on the $N$ photons, every $\beta$ and all $\alpha,\alpha'$,
--
--   $$
--   (U_\beta\rho U_\beta)_{\alpha,\alpha'}=(-1)^{(\alpha\oplus\alpha')\odot\beta}\,(\rho)_{\alpha,\alpha'},
--   $$
--
--   the matrices being taken in Bob's basis $\{|\psi_{\alpha,\hat\theta}\rangle\}$.
--
--   This says that $U_\beta$ is diagonal in Bob's basis, with signs given by the parity with $\beta$.
--
--   Differences from the source:
--   - encoding: the exponent (α ⊕ α′) ⊙ β in GF(2) → its value in {0, 1}; reason: Lean power needs a natural exponent; the sign is the same
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §9, (4), p.12

import Mathlib
import Definitions.Def_MayersQKD_rhoX

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §9, (4), p.12: for any operator `ρ` and any `β`, in Bob's
basis, `(U_β ρ U_β)_{α,α′} = (−1)^((α⊕α′)⊙β) (ρ)_{α,α′}`.

**Formalization Note.** Bob's basis is opposite to `θ` at every position (§9, p.11). The exponent is
the `GF(2)` value `(α ⊕ α′) ⊙ β`, read in `{0, 1}`. -/
theorem matEntry_shift {N : ℕ} (θ θhat : Bases N) (hθ : ∀ i, θhat i ≠ θ i) (β : Bits N)
    (ρ : Photons N →L[ℂ] Photons N) (α α' : Bits N) :
    matEntry θhat (shiftU θ β * ρ * shiftU θ β) α α' =
      (-1 : ℂ) ^ ((α + α') ⬝ᵥ β).val * matEntry θhat ρ α α' := by sorry

end MayersQKD
