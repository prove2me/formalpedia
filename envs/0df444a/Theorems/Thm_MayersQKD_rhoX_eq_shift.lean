-- Prove2me | Theorems.Thm_MayersQKD_rhoX_eq_shift
-- name    : MayersQKD.rhoX_eq_shift
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:24.203756+00:00
-- url     : https://prove2.me/theorems/aa7105db-244e-4c55-a5b9-b9c8dcc4f051
-- title:
--   (3), p.12 — $\rho_x=U_\beta\rho_{\mathbf 0}U_\beta$
-- statement:
--   Let $f$ be an $(r+m)\times N$ boolean matrix, $\theta$ a string of bases and $\beta\in C_x$. Since $C_x=C_{\mathbf 0}\oplus\beta$,
--
--   $$
--   \rho_x=U_\beta\,\rho_{\mathbf 0}\,U_\beta .
--   $$
--
--   So every $\rho_x$ is a conjugate of $\rho_{\mathbf 0}$, and its matrix in Bob's basis follows from that of $\rho_{\mathbf 0}$.
--
--   Differences from the source: none.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §9, (3), p.12

import Mathlib
import Definitions.Def_MayersQKD_rhoX

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §9, (3), p.12: for every `β ∈ C_x` we have `C_x = C₀ ⊕ β`,
hence `ρ_x = U_β ρ₀ U_β`. -/
theorem rhoX_eq_shift {N r m : ℕ} (f : HashMatrix r m N) (θ : Bases N)
    (x : Fin r ⊕ Fin m → ZMod 2) (β : Bits N) (hβ : f.mulVec β = x) :
    rhoX f θ x = shiftU θ β * rhoX f θ 0 * shiftU θ β := by sorry

end MayersQKD
