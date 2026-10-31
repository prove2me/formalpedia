-- Prove2me | Theorems.Thm_ObliviousRSP_eq_2
-- name    : ObliviousRSP.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:22.724287+00:00
-- url     : https://prove2.me/theorems/4266b8f3-f607-40c2-861c-63e65dc8b7ac
-- title:
--   Eq. (2) — Bob's half before the message is maximally mixed
-- statement:
--   Let $(E_m)_{m\in M}$ be any POVM that Alice applies to her half of $|\Phi_{d'}\rangle$. Then Bob's unnormalized conditional states sum to the maximally mixed state:
--   $$
--   \sum_{m} p_m\,\rho_{\varphi m} = \frac{I}{d'} ,
--   $$
--   where $p_m\rho_{\varphi m} = \operatorname{Tr}_1[(E_m\otimes I)|\Phi_{d'}\rangle\langle\Phi_{d'}|]$ and $d'$ is the dimension of each half.
--
--   This is the no-signalling identity: before receiving the message, Bob's half is in the state $I/d'$ whatever Alice did. Substituted with (1) it gives (3).
--
--   **Formalization Note** The sum is a `HasSum` over an arbitrary outcome type. When the half is zero-dimensional both sides are the empty matrix.
--
--   Differences from the source:
--   - generalization: Alice's POVM E_φ of the protocol → any POVM E′ on her half; reason: (2) uses only that Alice measures her half of |Φ_d′⟩; the protocol's E ψ is one such POVM
--   - encoding: normalized conditional state ρ_φm → unnormalized p_m ρ_φm (bobState (E ψ m)); reason: ρ_φm is undefined when p_m = 0; for p_m > 0 dividing by p_m gives the page's identity, and the unnormalized state is the paper's own b of (6); same instances
--   - generalization: sum over the messages m → HasSum over an arbitrary message type M; reason: covers finite and countably infinite message sets (p.5 allows messages of variable length); for a finite M it is the finite sum
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eq. (2), p.3

import Mathlib
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eq. (2), p.3: "describing in two different ways the state in Bob's half of the shared
system before receiving the message m, ∑m pmρφm = I/d′". For every POVM `E'` that Alice may
apply to her half of `|Φ_{d′}⟩`, Bob's unnormalized conditional states sum to the maximally mixed
state: `∑_m bobState (E' m) = I/d′`.

**Formalization Note.** Stated for an arbitrary POVM on `σ` (the protocol's `E ψ` is one) and an
arbitrary outcome type, with `HasSum`. `d′ = Fintype.card σ`; for an empty `σ` both sides are the
empty matrix. -/
theorem eq_2 {σ M : Type} [Fintype σ] [DecidableEq σ] (E' : M → Matrix σ σ ℂ)
    (hE : IsPOVM E') :
    HasSum (fun m => bobState (E' m)) ((Fintype.card σ : ℂ)⁻¹ • (1 : Matrix σ σ ℂ)) := by sorry

end ObliviousRSP
